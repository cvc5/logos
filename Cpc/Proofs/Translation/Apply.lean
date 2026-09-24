module

public import Cpc.Proofs.Translation.Datatypes
public import Cpc.Proofs.Translation.Quantifiers
public import Cpc.Proofs.Translation.Special
public import Cpc.Proofs.Translation.Inversions
public import Cpc.Proofs.Translation.Heads
public import Cpc.Proofs.Translation.EoTypeofCore
public import Cpc.Proofs.TypePreservation.Full
import all Cpc.Spec
import all Cpc.Proofs.TypePreservation.Datatypes

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace TranslationProofs

attribute [local simp] Smtm.__smtx_type_wf_component

private theorem smtx_type_wf_rec_of_type_wf
    {T : SmtType}
    (hNotReg : T ≠ SmtType.RegLan)
    (hNotFun : ∀ A B : SmtType, T ≠ SmtType.FunType A B)
    (hNotIFun : ∀ A B : SmtType, T ≠ SmtType.FunType A B)
    (h : __smtx_type_wf T = true) :
    __smtx_type_wf_rec T = true := by
  cases T <;> simp_all [__smtx_type_wf, __smtx_type_wf_component,
    __smtx_type_wf_rec, native_and]

private theorem smtx_type_field_wf_rec_ne_none
    {T : SmtType} {refs : RefList}
    (h : smtx_type_field_wf_rec T refs) : T ≠ SmtType.None := by
  intro hNone
  subst T
  simp [smtx_type_field_wf_rec, __smtx_type_wf_rec] at h

@[simp] private theorem native_inhabited_type_bool_apply :
    native_inhabited_type SmtType.Bool = true :=
  native_inhabited_type_bool

@[simp] private theorem native_inhabited_type_int_apply :
    native_inhabited_type SmtType.Int = true :=
  native_inhabited_type_int

@[simp] private theorem native_inhabited_type_real_apply :
    native_inhabited_type SmtType.Real = true :=
  native_inhabited_type_real

@[simp] private theorem native_inhabited_type_reglan_apply :
    native_inhabited_type SmtType.RegLan = true :=
  native_inhabited_type_reglan

@[simp] private theorem native_inhabited_type_char_apply :
    native_inhabited_type SmtType.Char = true :=
  native_inhabited_type_char

@[simp] private theorem native_inhabited_type_usort_apply
    (i : native_Nat) :
    native_inhabited_type (SmtType.USort i) = true :=
  native_inhabited_type_usort i

@[simp] private theorem native_inhabited_type_typeref_apply
    (s : native_String) :
    native_inhabited_type (SmtType.TypeRef s) = false := by
  simp [native_inhabited_type, native_Teq, native_not, __smtx_type_default,
    __smtx_typeof_value, native_and]

@[simp] private theorem native_inhabited_type_seq_apply
    (T : SmtType) :
    native_inhabited_type (SmtType.Seq T) = true :=
  native_inhabited_type_seq T

@[simp] private theorem native_inhabited_type_set_apply
    (T : SmtType) :
    native_inhabited_type (SmtType.Set T) = true :=
  native_inhabited_type_set T

@[simp] theorem native_inhabited_type_bitvec_apply
    (w : native_Nat) :
    native_inhabited_type (SmtType.BitVec w) = true := by
  simp [native_inhabited_type, native_not, native_Teq, __smtx_type_default,
    __smtx_typeof_value,
    native_and, native_zleq, native_zeq,
    native_mod_total, native_int_pow2, native_zexp_total, native_nat_to_int,
    native_int_to_nat, native_ite]

/-- Simplifies EO-to-SMT translation for `typeof_matches_translation_apply_concat`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_concat
    (x y : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.concat) y) x) =
        SmtTerm.concat (__eo_to_smt y) (__eo_to_smt x))
    (hEo :
      ∀ w1 w2 : native_Nat,
        __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w1 ->
        __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w2 ->
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.concat) y) x)) =
          SmtType.BitVec
            (native_int_to_nat (native_zplus (native_nat_to_int w1) (native_nat_to_int w2))))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.concat) y) x)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.concat) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.concat) y) x)) := by
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.concat (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases bv_concat_args_of_non_none hApplyNN with ⟨w1, w2, hy, hx⟩
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.concat) y) x)) =
        SmtType.BitVec
          (native_int_to_nat (native_zplus (native_nat_to_int w1) (native_nat_to_int w2))) := by
    rw [hTranslate]
    rw [typeof_concat_eq (__eo_to_smt y) (__eo_to_smt x)]
    simp [__smtx_typeof_concat, hy, hx]
  exact hSmt.trans (hEo w1 w2 hy hx).symm

/-- Simplifies EO-to-SMT translation for `typeof_matches_translation_apply_bv_binop`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_bv_binop
    (eoOp : Term) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (x y : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply eoOp y) x) =
        smtOp (__eo_to_smt y) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x)))
    (hEo :
      ∀ w : native_Nat,
        __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
        __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply eoOp y) x)) = SmtType.BitVec w)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply eoOp y) x)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply eoOp y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply eoOp y) x)) := by
  have hApplyNN :
      term_has_non_none_type
        (smtOp (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases bv_binop_args_of_non_none hTy hApplyNN with ⟨w, hy, hx⟩
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply eoOp y) x)) = SmtType.BitVec w := by
    rw [hTranslate]
    rw [hTy, hy, hx]
    simp [__smtx_typeof_bv_op_2, native_ite, native_nateq, Smtm.native_nateq]
  exact hSmt.trans (hEo w hy hx).symm

/-- Simplifies EO-to-SMT translation for `typeof_matches_translation_apply_bv_binop_ret`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
    (eoOp : Term) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (ret : SmtType) (x y : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply eoOp y) x) =
        smtOp (__eo_to_smt y) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_bv_op_2_ret (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x))
          ret)
    (hEo :
      ∀ w : native_Nat,
        __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
        __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply eoOp y) x)) = ret)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply eoOp y) x)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply eoOp y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply eoOp y) x)) := by
  have hApplyNN :
      term_has_non_none_type
        (smtOp (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases bv_binop_ret_args_of_non_none hTy hApplyNN with
    ⟨w, hy, hx⟩
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply eoOp y) x)) = ret := by
    rw [hTranslate]
    rw [hTy, hy, hx]
    simp [__smtx_typeof_bv_op_2_ret, native_ite, native_nateq, Smtm.native_nateq]
  exact hSmt.trans (hEo w hy hx).symm

/-- Simplifies comparison operators translated through an `ite` returning `(_ BitVec 1)`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_bv_cmp_to_bv1
    (eoOp : Term) (smtCmp : SmtTerm -> SmtTerm -> SmtTerm) (x y : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply eoOp y) x) =
        SmtTerm.ite (smtCmp (__eo_to_smt y) (__eo_to_smt x))
          (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0))
    (hTy :
      __smtx_typeof (smtCmp (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_bv_op_2_ret
          (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x))
          SmtType.Bool)
    (hEo :
      ∀ w : native_Nat,
        __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
        __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply eoOp y) x)) =
          SmtType.BitVec 1)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply eoOp y) x)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply eoOp y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply eoOp y) x)) := by
  have hIteNN :
      term_has_non_none_type
        (SmtTerm.ite (smtCmp (__eo_to_smt y) (__eo_to_smt x))
          (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases ite_args_of_non_none hIteNN with ⟨T, hCond, hThen, hElse, hT⟩
  have hCmpNN :
      term_has_non_none_type (smtCmp (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [hCond]
    simp
  rcases bv_binop_ret_args_of_non_none hTy hCmpNN with ⟨w, hy, hx⟩
  have hCmpTy :
      __smtx_typeof (smtCmp (__eo_to_smt y) (__eo_to_smt x)) = SmtType.Bool := by
    rw [hTy, hy, hx]
    simp [__smtx_typeof_bv_op_2_ret, native_ite, native_nateq, Smtm.native_nateq]
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply eoOp y) x)) =
        SmtType.BitVec 1 := by
    rw [hTranslate, typeof_ite_eq, hCmpTy]
    have hThen : __smtx_typeof (SmtTerm.Binary 1 1) = SmtType.BitVec 1 := by
      have hWidth : native_zleq 0 1 = true := by native_decide
      have hMod : native_zeq 1 (native_mod_total 1 (native_int_pow2 1)) = true := by
        native_decide
      have hNat : native_int_to_nat 1 = 1 := by native_decide
      simp [__smtx_typeof, native_ite, native_and, hWidth, hMod, hNat]
    have hElse : __smtx_typeof (SmtTerm.Binary 1 0) = SmtType.BitVec 1 := by
      have hWidth : native_zleq 0 1 = true := by native_decide
      have hMod : native_zeq 0 (native_mod_total 0 (native_int_pow2 1)) = true := by
        native_decide
      have hNat : native_int_to_nat 1 = 1 := by native_decide
      simp [__smtx_typeof, native_ite, native_and, hWidth, hMod, hNat]
    rw [hThen, hElse]
    simp [__smtx_typeof_ite, native_ite, native_Teq]
  exact hSmt.trans (hEo w hy hx).symm

/-- Extracts non-`none` from a function-like apply head. -/
private theorem smtx_head_non_none_of_apply_cases
    {T A B : SmtType}
    (hHead :
      T = SmtType.FunType A B ∨ T = SmtType.DtcAppType A B) :
  T ≠ SmtType.None := by
  intro hNone
  rcases hHead with hHead | hHead
  · cases hNone.symm.trans hHead
  · cases hNone.symm.trans hHead

/-- Computes `__smtx_typeof_apply` for function-like apply heads. -/
private theorem smtx_typeof_apply_of_head_cases
    {F X A B : SmtType}
    (hHead :
      F = SmtType.FunType A B ∨ F = SmtType.DtcAppType A B)
    (hX : X = A)
    (hA : A ≠ SmtType.None) :
    __smtx_typeof_apply F X = B := by
  rcases hHead with hHead | hHead
  · rw [hHead, hX]
    simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hA]
  · rw [hHead, hX]
    simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hA]

/-- Rewrites `generic_apply_type` for heads that are not datatype selectors/testers. -/
private theorem generic_apply_type_of_non_special_head
    (f x : SmtTerm)
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i) :
    generic_apply_type f x := by
  unfold generic_apply_type
  cases f <;>
    first
    | exact absurd rfl (hSel _ _ _ _)
    | exact absurd rfl (hTester _ _ _)
    | simp [__smtx_typeof]

private theorem eo_to_smt_distinct_ne_dt_sel
    (xs : Term) (s : native_String) (d : SmtDatatypeDecl) (i j : native_Nat) :
    __eo_to_smt_distinct xs ≠ SmtTerm.DtSel s d i j := by
  intro h
  cases xs <;> try cases h
  case Apply f x =>
    cases f <;> try cases h
    case UOp op =>
      cases op <;> cases h
    case Apply g y =>
      cases g <;> try cases h
      case UOp op =>
        cases op <;> cases h

private theorem eo_to_smt_distinct_ne_dt_tester
    (xs : Term) (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    __eo_to_smt_distinct xs ≠ SmtTerm.DtTester s d i := by
  intro h
  cases xs <;> try cases h
  case Apply f x =>
    cases f <;> try cases h
    case UOp op =>
      cases op <;> cases h
    case Apply g y =>
      cases g <;> try cases h
      case UOp op =>
        cases op <;> cases h

private theorem eo_to_smt_distinct_ne_dt_cons
    (xs : Term) (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    __eo_to_smt_distinct xs ≠ SmtTerm.DtCons s d i := by
  intro h
  cases xs <;> try cases h
  case Apply f x =>
    cases f <;> try cases h
    case UOp op =>
      cases op <;> cases h
    case Apply g y =>
      cases g <;> try cases h
      case UOp op =>
        cases op <;> cases h

private theorem eo_to_smt_distinct_top_ne_dt_sel
    (xs : Term) (s : native_String) (d : SmtDatatypeDecl) (i j : native_Nat) :
    __eo_to_smt (Term.Apply (Term.UOp UserOp.distinct) xs) ≠ SmtTerm.DtSel s d i j := by
  intro h
  change
    native_ite (native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None)
      SmtTerm.None (__eo_to_smt_distinct xs) =
      SmtTerm.DtSel s d i j at h
  cases hGuard : native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None
  · simp [native_ite, hGuard] at h
    exact eo_to_smt_distinct_ne_dt_sel xs s d i j h
  · simp [native_ite, hGuard] at h

private theorem eo_to_smt_distinct_top_ne_dt_tester
    (xs : Term) (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    __eo_to_smt (Term.Apply (Term.UOp UserOp.distinct) xs) ≠ SmtTerm.DtTester s d i := by
  intro h
  change
    native_ite (native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None)
      SmtTerm.None (__eo_to_smt_distinct xs) =
      SmtTerm.DtTester s d i at h
  cases hGuard : native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None
  · simp [native_ite, hGuard] at h
    exact eo_to_smt_distinct_ne_dt_tester xs s d i h
  · simp [native_ite, hGuard] at h

private theorem eo_to_smt_distinct_top_ne_dt_cons
    (xs : Term) (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    __eo_to_smt (Term.Apply (Term.UOp UserOp.distinct) xs) ≠ SmtTerm.DtCons s d i := by
  intro h
  change
    native_ite (native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None)
      SmtTerm.None (__eo_to_smt_distinct xs) =
      SmtTerm.DtCons s d i at h
  cases hGuard : native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None
  · simp [native_ite, hGuard] at h
    exact eo_to_smt_distinct_ne_dt_cons xs s d i h
  · simp [native_ite, hGuard] at h

private theorem eo_to_smt_at_bv_ne_dt_sel
    (a b : SmtTerm) (s : native_String) (d : SmtDatatypeDecl) (i j : native_Nat) :
    SmtTerm.int_to_bv b a ≠ SmtTerm.DtSel s d i j := by
  intro h
  cases h

private theorem eo_to_smt_at_bv_ne_dt_tester
    (a b : SmtTerm) (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    SmtTerm.int_to_bv b a ≠ SmtTerm.DtTester s d i := by
  intro h
  cases h

private theorem eo_to_smt_array_deq_diff_ne_dt_sel
    (a b : SmtTerm) (s : native_String) (d : SmtDatatypeDecl)
    (i j : native_Nat) :
    __eo_to_smt_array_deq_diff a (__smtx_typeof a) b (__smtx_typeof b) ≠
      SmtTerm.DtSel s d i j := by
  intro h
  cases ha : __smtx_typeof a <;> cases hb : __smtx_typeof b <;>
    simp [__eo_to_smt_array_deq_diff, ha, hb] at h <;>
    cases h

private theorem eo_to_smt_array_deq_diff_ne_dt_tester
    (a b : SmtTerm) (s : native_String) (d : SmtDatatypeDecl)
    (i : native_Nat) :
    __eo_to_smt_array_deq_diff a (__smtx_typeof a) b (__smtx_typeof b) ≠
      SmtTerm.DtTester s d i := by
  intro h
  cases ha : __smtx_typeof a <;> cases hb : __smtx_typeof b <;>
    simp [__eo_to_smt_array_deq_diff, ha, hb] at h <;>
    cases h

private theorem eo_to_smt_array_deq_diff_ne_dt_cons
    (a b : SmtTerm) (s : native_String) (d : SmtDatatypeDecl)
    (i : native_Nat) :
    __eo_to_smt_array_deq_diff a (__smtx_typeof a) b (__smtx_typeof b) ≠
      SmtTerm.DtCons s d i := by
  intro h
  cases ha : __smtx_typeof a <;> cases hb : __smtx_typeof b <;>
    simp [__eo_to_smt_array_deq_diff, ha, hb] at h <;>
    cases h

private theorem eo_to_smt_sets_deq_diff_ne_dt_sel
    (a b : SmtTerm) (s : native_String) (d : SmtDatatypeDecl)
    (i j : native_Nat) :
    __eo_to_smt_sets_deq_diff a (__smtx_typeof a) b (__smtx_typeof b) ≠
      SmtTerm.DtSel s d i j := by
  intro h
  cases ha : __smtx_typeof a <;> cases hb : __smtx_typeof b <;>
    simp [__eo_to_smt_sets_deq_diff, ha, hb] at h <;>
    cases h

private theorem eo_to_smt_sets_deq_diff_ne_dt_tester
    (a b : SmtTerm) (s : native_String) (d : SmtDatatypeDecl)
    (i : native_Nat) :
    __eo_to_smt_sets_deq_diff a (__smtx_typeof a) b (__smtx_typeof b) ≠
      SmtTerm.DtTester s d i := by
  intro h
  cases ha : __smtx_typeof a <;> cases hb : __smtx_typeof b <;>
    simp [__eo_to_smt_sets_deq_diff, ha, hb] at h <;>
    cases h

private theorem eo_to_smt_sets_deq_diff_ne_dt_cons
    (a b : SmtTerm) (s : native_String) (d : SmtDatatypeDecl)
    (i : native_Nat) :
    __eo_to_smt_sets_deq_diff a (__smtx_typeof a) b (__smtx_typeof b) ≠
      SmtTerm.DtCons s d i := by
  intro h
  cases ha : __smtx_typeof a <;> cases hb : __smtx_typeof b <;>
    simp [__eo_to_smt_sets_deq_diff, ha, hb] at h <;>
    cases h

private theorem eo_to_smt_tuple_select_ne_dt_sel
    (T : SmtType) (n t : SmtTerm) (s : native_String) (d : SmtDatatypeDecl)
    (i j : native_Nat) :
    __eo_to_smt_tuple_select T n t ≠ SmtTerm.DtSel s d i j := by
  intro h
  simp [__eo_to_smt_tuple_select] at h
  split at h <;> try cases h
  case h_1 =>
    unfold native_ite at h
    split at h <;> cases h

private theorem eo_to_smt_tuple_select_ne_dt_tester
    (T : SmtType) (n t : SmtTerm) (s : native_String) (d : SmtDatatypeDecl)
    (i : native_Nat) :
    __eo_to_smt_tuple_select T n t ≠ SmtTerm.DtTester s d i := by
  intro h
  simp [__eo_to_smt_tuple_select] at h
  split at h <;> try cases h
  case h_1 =>
    unfold native_ite at h
    split at h <;> cases h

private theorem eo_to_smt_tuple_select_ne_dt_cons
    (T : SmtType) (n t : SmtTerm) (s : native_String) (d : SmtDatatypeDecl)
    (i : native_Nat) :
    __eo_to_smt_tuple_select T n t ≠ SmtTerm.DtCons s d i := by
  intro h
  simp [__eo_to_smt_tuple_select] at h
  split at h <;> try cases h
  case h_1 =>
    unfold native_ite at h
    split at h <;> cases h

private theorem eo_to_smt_updater_ne_dt_sel
    (sel t u : SmtTerm) (s : native_String) (d : SmtDatatypeDecl) (i j : native_Nat) :
    __eo_to_smt_updater sel t u ≠ SmtTerm.DtSel s d i j := by
  intro h
  cases sel <;> try cases h
  case DtSel s' d' i' j' =>
    cases hIdx : native_zlt (native_nat_to_int j')
        (native_nat_to_int (__smtx_dt_num_sels (__smtx_dd_lookup s' d') i')) <;>
      simp [__eo_to_smt_updater, native_ite, hIdx] at h

private theorem eo_to_smt_updater_ne_dt_tester
    (sel t u : SmtTerm) (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    __eo_to_smt_updater sel t u ≠ SmtTerm.DtTester s d i := by
  intro h
  cases sel <;> try cases h
  case DtSel s' d' i' j' =>
    cases hIdx : native_zlt (native_nat_to_int j')
        (native_nat_to_int (__smtx_dt_num_sels (__smtx_dd_lookup s' d') i')) <;>
      simp [__eo_to_smt_updater, native_ite, hIdx] at h

private theorem eo_to_smt_updater_ne_dt_cons
    (sel t u : SmtTerm) (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    __eo_to_smt_updater sel t u ≠ SmtTerm.DtCons s d i := by
  intro h
  cases sel <;> try cases h
  case DtSel s' d' i' j' =>
    cases hIdx : native_zlt (native_nat_to_int j')
        (native_nat_to_int (__smtx_dt_num_sels (__smtx_dd_lookup s' d') i')) <;>
      simp [__eo_to_smt_updater, native_ite, hIdx] at h

private theorem eo_to_smt_tuple_update_ne_dt_sel
    (T : SmtType) (n t u : SmtTerm) (s : native_String) (d : SmtDatatypeDecl)
    (i j : native_Nat) :
    __eo_to_smt_tuple_update T n t u ≠ SmtTerm.DtSel s d i j := by
  intro h
  simp [__eo_to_smt_tuple_update] at h
  split at h <;> try cases h
  case h_1 =>
    unfold native_ite at h
    split at h
    · exact eo_to_smt_updater_ne_dt_sel _ _ _ _ _ _ _ h
    · cases h

private theorem eo_to_smt_tuple_update_ne_dt_tester
    (T : SmtType) (n t u : SmtTerm) (s : native_String) (d : SmtDatatypeDecl)
    (i : native_Nat) :
    __eo_to_smt_tuple_update T n t u ≠ SmtTerm.DtTester s d i := by
  intro h
  simp [__eo_to_smt_tuple_update] at h
  split at h <;> try cases h
  case h_1 =>
    unfold native_ite at h
    split at h
    · exact eo_to_smt_updater_ne_dt_tester _ _ _ _ _ _ h
    · cases h

private theorem eo_to_smt_tuple_update_ne_dt_cons
    (T : SmtType) (n t u : SmtTerm) (s : native_String) (d : SmtDatatypeDecl)
    (i : native_Nat) :
    __eo_to_smt_tuple_update T n t u ≠ SmtTerm.DtCons s d i := by
  intro h
  simp [__eo_to_smt_tuple_update] at h
  split at h <;> try cases h
  case h_1 =>
    unfold native_ite at h
    split at h
    · exact eo_to_smt_updater_ne_dt_cons _ _ _ _ _ _ h
    · cases h

private theorem eo_to_smt_tuple_prepend_rec_ne_dt_sel
    (tailDD : SmtDatatypeDecl) (tailD : SmtDatatype)
    (tail : SmtTerm) (k : native_Nat)
    (acc : SmtTerm)
    (hAcc : ∀ s d i j, acc ≠ SmtTerm.DtSel s d i j)
    (s : native_String) (d : SmtDatatypeDecl) (i j : native_Nat) :
    __eo_to_smt_tuple_prepend_rec tailDD tailD tail k acc ≠
      SmtTerm.DtSel s d i j := by
  intro h
  cases k with
  | zero =>
      exact hAcc s d i j h
  | succ k =>
      simp [__eo_to_smt_tuple_prepend_rec] at h

private theorem eo_to_smt_tuple_prepend_rec_ne_dt_tester
    (tailDD : SmtDatatypeDecl) (tailD : SmtDatatype)
    (tail : SmtTerm) (k : native_Nat)
    (acc : SmtTerm)
    (hAcc : ∀ s d i, acc ≠ SmtTerm.DtTester s d i)
    (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    __eo_to_smt_tuple_prepend_rec tailDD tailD tail k acc ≠
      SmtTerm.DtTester s d i := by
  intro h
  cases k with
  | zero =>
      exact hAcc s d i h
  | succ k =>
      simp [__eo_to_smt_tuple_prepend_rec] at h

private theorem eo_to_smt_tuple_prepend_rec_ne_dt_cons
    (tailDD : SmtDatatypeDecl) (tailD : SmtDatatype)
    (tail : SmtTerm) (k : native_Nat)
    (acc : SmtTerm)
    (hAcc : ∀ s d i, acc ≠ SmtTerm.DtCons s d i)
    (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    __eo_to_smt_tuple_prepend_rec tailDD tailD tail k acc ≠
      SmtTerm.DtCons s d i := by
  intro h
  cases k with
  | zero =>
      exact hAcc s d i h
  | succ k =>
      simp [__eo_to_smt_tuple_prepend_rec] at h

private theorem eo_to_smt_tuple_prepend_of_type_ne_dt_sel
    (tailTy : SmtType) (head : SmtTerm) (headTy : SmtType)
    (tail : SmtTerm) (s : native_String) (d : SmtDatatypeDecl)
    (i j : native_Nat) :
    __eo_to_smt_tuple_prepend_of_type tailTy head headTy tail ≠
      SmtTerm.DtSel s d i j := by
  intro h
  cases tailTy <;> try simp [__eo_to_smt_tuple_prepend_of_type] at h
  case Datatype sTail ddTail =>
    cases ddTail with
    | nil => simp at h
    | cons s2 dTail ddRest =>
      cases ddRest with
      | cons s3 d3 dd3 => simp at h
      | nil =>
        cases dTail with
        | null => simp at h
        | sum c rest =>
          cases rest with
          | sum cRest restRest => simp at h
          | null =>
            simp only at h
            cases hCond : native_and
                (native_and (native_streq sTail (native_string_lit "@Tuple"))
                  (native_streq s2 (native_string_lit "@Tuple")))
                (__smtx_type_wf
                  (SmtType.Datatype (native_string_lit "@Tuple")
                    (__eo_to_smt_tuple_decl
                      (SmtDatatype.sum (SmtDatatypeCons.cons headTy c)
                        SmtDatatype.null)))) with
            | false => simp [hCond, native_ite] at h
            | true =>
              simp [hCond, native_ite] at h
              exact eo_to_smt_tuple_prepend_rec_ne_dt_sel
                (__eo_to_smt_tuple_decl (SmtDatatype.sum c SmtDatatype.null))
                (SmtDatatype.sum c SmtDatatype.null) tail
                (__smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null) 0)
                (SmtTerm.Apply
                  (SmtTerm.DtCons (native_string_lit "@Tuple")
                    (__eo_to_smt_tuple_decl
                      (SmtDatatype.sum (SmtDatatypeCons.cons headTy c)
                        SmtDatatype.null)) 0) head)
                (by intro s0 d0 i0 j0 hSeed; cases hSeed) s d i j h

private theorem eo_to_smt_tuple_prepend_of_type_ne_dt_tester
    (tailTy : SmtType) (head : SmtTerm) (headTy : SmtType)
    (tail : SmtTerm) (s : native_String) (d : SmtDatatypeDecl)
    (i : native_Nat) :
    __eo_to_smt_tuple_prepend_of_type tailTy head headTy tail ≠
      SmtTerm.DtTester s d i := by
  intro h
  cases tailTy <;> try simp [__eo_to_smt_tuple_prepend_of_type] at h
  case Datatype sTail ddTail =>
    cases ddTail with
    | nil => simp at h
    | cons s2 dTail ddRest =>
      cases ddRest with
      | cons s3 d3 dd3 => simp at h
      | nil =>
        cases dTail with
        | null => simp at h
        | sum c rest =>
          cases rest with
          | sum cRest restRest => simp at h
          | null =>
            simp only at h
            cases hCond : native_and
                (native_and (native_streq sTail (native_string_lit "@Tuple"))
                  (native_streq s2 (native_string_lit "@Tuple")))
                (__smtx_type_wf
                  (SmtType.Datatype (native_string_lit "@Tuple")
                    (__eo_to_smt_tuple_decl
                      (SmtDatatype.sum (SmtDatatypeCons.cons headTy c)
                        SmtDatatype.null)))) with
            | false => simp [hCond, native_ite] at h
            | true =>
              simp [hCond, native_ite] at h
              exact eo_to_smt_tuple_prepend_rec_ne_dt_tester
                (__eo_to_smt_tuple_decl (SmtDatatype.sum c SmtDatatype.null))
                (SmtDatatype.sum c SmtDatatype.null) tail
                (__smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null) 0)
                (SmtTerm.Apply
                  (SmtTerm.DtCons (native_string_lit "@Tuple")
                    (__eo_to_smt_tuple_decl
                      (SmtDatatype.sum (SmtDatatypeCons.cons headTy c)
                        SmtDatatype.null)) 0) head)
                (by intro s0 d0 i0 hSeed; cases hSeed) s d i h

private theorem eo_to_smt_tuple_prepend_of_type_ne_dt_cons
    (tailTy : SmtType) (head : SmtTerm) (headTy : SmtType)
    (tail : SmtTerm) (s : native_String) (d : SmtDatatypeDecl)
    (i : native_Nat) :
    __eo_to_smt_tuple_prepend_of_type tailTy head headTy tail ≠
      SmtTerm.DtCons s d i := by
  intro h
  cases tailTy <;> try simp [__eo_to_smt_tuple_prepend_of_type] at h
  case Datatype sTail ddTail =>
    cases ddTail with
    | nil => simp at h
    | cons s2 dTail ddRest =>
      cases ddRest with
      | cons s3 d3 dd3 => simp at h
      | nil =>
        cases dTail with
        | null => simp at h
        | sum c rest =>
          cases rest with
          | sum cRest restRest => simp at h
          | null =>
            simp only at h
            cases hCond : native_and
                (native_and (native_streq sTail (native_string_lit "@Tuple"))
                  (native_streq s2 (native_string_lit "@Tuple")))
                (__smtx_type_wf
                  (SmtType.Datatype (native_string_lit "@Tuple")
                    (__eo_to_smt_tuple_decl
                      (SmtDatatype.sum (SmtDatatypeCons.cons headTy c)
                        SmtDatatype.null)))) with
            | false => simp [hCond, native_ite] at h
            | true =>
              simp [hCond, native_ite] at h
              exact eo_to_smt_tuple_prepend_rec_ne_dt_cons
                (__eo_to_smt_tuple_decl (SmtDatatype.sum c SmtDatatype.null))
                (SmtDatatype.sum c SmtDatatype.null) tail
                (__smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null) 0)
                (SmtTerm.Apply
                  (SmtTerm.DtCons (native_string_lit "@Tuple")
                    (__eo_to_smt_tuple_decl
                      (SmtDatatype.sum (SmtDatatypeCons.cons headTy c)
                        SmtDatatype.null)) 0) head)
                (by intro s0 d0 i0 hSeed; cases hSeed) s d i h

theorem eo_to_smt_tuple_prepend_ne_dt_sel
    (head : SmtTerm) (headTy : SmtType) (tail : SmtTerm)
    (s : native_String) (d : SmtDatatypeDecl) (i j : native_Nat) :
    __eo_to_smt_tuple_prepend head headTy tail ≠ SmtTerm.DtSel s d i j := by
  intro h
  exact
    eo_to_smt_tuple_prepend_of_type_ne_dt_sel
      (__smtx_typeof tail) head headTy tail s d i j h

theorem eo_to_smt_tuple_prepend_ne_dt_tester
    (head : SmtTerm) (headTy : SmtType) (tail : SmtTerm)
    (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    __eo_to_smt_tuple_prepend head headTy tail ≠ SmtTerm.DtTester s d i := by
  intro h
  exact
    eo_to_smt_tuple_prepend_of_type_ne_dt_tester
      (__smtx_typeof tail) head headTy tail s d i h

private theorem eo_to_smt_tuple_prepend_ne_dt_cons
    (head : SmtTerm) (headTy : SmtType) (tail : SmtTerm)
    (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    __eo_to_smt_tuple_prepend head headTy tail ≠ SmtTerm.DtCons s d i := by
  intro h
  exact
    eo_to_smt_tuple_prepend_of_type_ne_dt_cons
      (__smtx_typeof tail) head headTy tail s d i h

theorem eo_to_smt_tuple_ne_dt_sel
    (x y : Term) (s : native_String) (d : SmtDatatypeDecl) (i j : native_Nat) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) y) x) ≠
      SmtTerm.DtSel s d i j := by
  intro h
  have h' :
      __eo_to_smt_tuple_prepend (__eo_to_smt y)
          (__smtx_typeof (__eo_to_smt y)) (__eo_to_smt x) =
        SmtTerm.DtSel s d i j := by
    change
      __eo_to_smt_tuple_prepend (__eo_to_smt y)
          (__smtx_typeof (__eo_to_smt y)) (__eo_to_smt x) =
        SmtTerm.DtSel s d i j at h
    exact h
  exact eo_to_smt_tuple_prepend_ne_dt_sel
    (__eo_to_smt y) (__smtx_typeof (__eo_to_smt y)) (__eo_to_smt x) s d i j h'

theorem eo_to_smt_tuple_ne_dt_tester
    (x y : Term) (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) y) x) ≠
      SmtTerm.DtTester s d i := by
  intro h
  have h' :
      __eo_to_smt_tuple_prepend (__eo_to_smt y)
          (__smtx_typeof (__eo_to_smt y)) (__eo_to_smt x) =
        SmtTerm.DtTester s d i := by
    change
      __eo_to_smt_tuple_prepend (__eo_to_smt y)
          (__smtx_typeof (__eo_to_smt y)) (__eo_to_smt x) =
        SmtTerm.DtTester s d i at h
    exact h
  exact eo_to_smt_tuple_prepend_ne_dt_tester
    (__eo_to_smt y) (__smtx_typeof (__eo_to_smt y)) (__eo_to_smt x) s d i h'

private theorem eo_to_smt_tuple_ne_dt_cons
    (x y : Term) (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) y) x) ≠
      SmtTerm.DtCons s d i := by
  intro h
  have h' :
      __eo_to_smt_tuple_prepend (__eo_to_smt y)
          (__smtx_typeof (__eo_to_smt y)) (__eo_to_smt x) =
        SmtTerm.DtCons s d i := by
    change
      __eo_to_smt_tuple_prepend (__eo_to_smt y)
          (__smtx_typeof (__eo_to_smt y)) (__eo_to_smt x) =
        SmtTerm.DtCons s d i at h
    exact h
  exact eo_to_smt_tuple_prepend_ne_dt_cons
    (__eo_to_smt y) (__smtx_typeof (__eo_to_smt y)) (__eo_to_smt x) s d i h'

private theorem eo_to_smt_re_unfold_ne_dt_sel
    (str re : SmtTerm) (n : native_Nat)
    (s : native_String) (d : SmtDatatypeDecl) (i j : native_Nat) :
    __eo_to_smt_re_unfold_pos_component str re n ≠ SmtTerm.DtSel s d i j := by
  induction n generalizing str re with
  | zero =>
      intro h
      cases re <;> simp [__eo_to_smt_re_unfold_pos_component] at h
  | succ n ih =>
      intro h
      cases re <;> simp [__eo_to_smt_re_unfold_pos_component] at h
      case re_concat r1 r2 =>
        exact ih _ _ h

private theorem eo_to_smt_re_unfold_ne_dt_tester
    (str re : SmtTerm) (n : native_Nat)
    (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    __eo_to_smt_re_unfold_pos_component str re n ≠ SmtTerm.DtTester s d i := by
  induction n generalizing str re with
  | zero =>
      intro h
      cases re <;> simp [__eo_to_smt_re_unfold_pos_component] at h
  | succ n ih =>
      intro h
      cases re <;> simp [__eo_to_smt_re_unfold_pos_component] at h
      case re_concat r1 r2 =>
        exact ih _ _ h

private theorem eo_to_smt_re_unfold_ne_dt_cons
    (str re : SmtTerm) (n : native_Nat)
    (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    __eo_to_smt_re_unfold_pos_component str re n ≠ SmtTerm.DtCons s d i := by
  induction n generalizing str re with
  | zero =>
      intro h
      cases re <;> simp [__eo_to_smt_re_unfold_pos_component] at h
  | succ n ih =>
      intro h
      cases re <;> simp [__eo_to_smt_re_unfold_pos_component] at h
      case re_concat r1 r2 =>
        exact ih _ _ h

private theorem eo_to_smt_quant_skolemize_ne_dt_sel
    (vs : Term) (G : SmtTerm) (n : native_Nat)
    (s : native_String) (d : SmtDatatypeDecl) (i j : native_Nat) :
    __eo_to_smt_quantifiers_skolemize vs G n ≠ SmtTerm.DtSel s d i j := by
  induction n generalizing vs G with
  | zero =>
      intro h
      unfold __eo_to_smt_quantifiers_skolemize at h
      split at h <;> simp_all
  | succ n ih =>
      intro h
      unfold __eo_to_smt_quantifiers_skolemize at h
      split at h <;> first | exact ih _ _ h | simp_all

private theorem eo_to_smt_quant_skolemize_ne_dt_tester
    (vs : Term) (G : SmtTerm) (n : native_Nat)
    (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    __eo_to_smt_quantifiers_skolemize vs G n ≠ SmtTerm.DtTester s d i := by
  induction n generalizing vs G with
  | zero =>
      intro h
      unfold __eo_to_smt_quantifiers_skolemize at h
      split at h <;> simp_all
  | succ n ih =>
      intro h
      unfold __eo_to_smt_quantifiers_skolemize at h
      split at h <;> first | exact ih _ _ h | simp_all

private theorem eo_to_smt_quant_skolemize_ne_dt_cons
    (vs : Term) (G : SmtTerm) (n : native_Nat)
    (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    __eo_to_smt_quantifiers_skolemize vs G n ≠ SmtTerm.DtCons s d i := by
  induction n generalizing vs G with
  | zero =>
      intro h
      unfold __eo_to_smt_quantifiers_skolemize at h
      split at h <;> simp_all
  | succ n ih =>
      intro h
      unfold __eo_to_smt_quantifiers_skolemize at h
      split at h <;> first | exact ih _ _ h | simp_all

private theorem smt_type_eq_of_native_Teq_true
    {A B : SmtType} (h : native_Teq A B = true) : A = B := by
  simpa [native_Teq] using h

private theorem smtx_typeof_dt_cons_rec_datatype_ne_set
    (s : native_String) (base : SmtDatatypeDecl) :
    ∀ (d : SmtDatatype) (i : native_Nat) (A : SmtType),
      __smtx_typeof_dt_cons_rec (SmtType.Datatype s base) d i ≠ SmtType.Set A
  | SmtDatatype.null, i, A => by
      cases i <;> simp [__smtx_typeof_dt_cons_rec]
  | SmtDatatype.sum c d, native_nat_zero, A => by
      cases c <;> simp [__smtx_typeof_dt_cons_rec]
  | SmtDatatype.sum c d, native_nat_succ n, A => by
      simpa [__smtx_typeof_dt_cons_rec] using
        smtx_typeof_dt_cons_rec_datatype_ne_set s base d n A

private theorem smtx_typeof_dt_cons_ne_set
    (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) (A : SmtType) :
    __smtx_typeof (SmtTerm.DtCons s d i) ≠ SmtType.Set A := by
  intro h
  rw [Smtm.typeof_dt_cons_eq] at h
  cases hWf : __smtx_type_wf (SmtType.Datatype s d) <;>
    simp [__smtx_typeof_guard_wf, hWf, native_ite] at h
  exact smtx_typeof_dt_cons_rec_datatype_ne_set
    s d (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i A h

private theorem eo_to_smt_set_insert_typed_nil_ne_dt_sel
    (T x : Term) (s : native_String) (d : SmtDatatypeDecl) (i j : native_Nat) :
    __eo_to_smt_set_insert
        (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) T)
        (__eo_to_smt x) ≠
      SmtTerm.DtSel s d i j := by
  intro h
  cases hTy :
      native_Teq (__smtx_typeof (__eo_to_smt x))
        (SmtType.Set (__eo_to_smt_type T))
  · simp [__eo_to_smt_set_insert, hTy, native_ite] at h
  · have hEq := smt_type_eq_of_native_Teq_true hTy
    simp [__eo_to_smt_set_insert, hTy, native_ite] at h
    rw [h] at hEq
    have hNone : __smtx_typeof (SmtTerm.DtSel s d i j) = SmtType.None := by
      rw [__smtx_typeof.eq_def]
    rw [hNone] at hEq
    cases hEq

private theorem eo_to_smt_set_insert_typed_nil_ne_dt_tester
    (T x : Term) (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    __eo_to_smt_set_insert
        (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) T)
        (__eo_to_smt x) ≠
      SmtTerm.DtTester s d i := by
  intro h
  cases hTy :
      native_Teq (__smtx_typeof (__eo_to_smt x))
        (SmtType.Set (__eo_to_smt_type T))
  · simp [__eo_to_smt_set_insert, hTy, native_ite] at h
  · have hEq := smt_type_eq_of_native_Teq_true hTy
    simp [__eo_to_smt_set_insert, hTy, native_ite] at h
    rw [h] at hEq
    have hNone : __smtx_typeof (SmtTerm.DtTester s d i) = SmtType.None := by
      rw [__smtx_typeof.eq_def]
    rw [hNone] at hEq
    cases hEq

private theorem eo_to_smt_set_insert_typed_nil_ne_dt_cons
    (T x : Term) (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    __eo_to_smt_set_insert
        (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) T)
        (__eo_to_smt x) ≠
      SmtTerm.DtCons s d i := by
  intro h
  cases hTy :
      native_Teq (__smtx_typeof (__eo_to_smt x))
        (SmtType.Set (__eo_to_smt_type T))
  · simp [__eo_to_smt_set_insert, hTy, native_ite] at h
  · have hEq := smt_type_eq_of_native_Teq_true hTy
    simp [__eo_to_smt_set_insert, hTy, native_ite] at h
    rw [h] at hEq
    exact smtx_typeof_dt_cons_ne_set s d i (__eo_to_smt_type T) hEq

private theorem eo_to_smt_set_insert_top_ne_dt_sel
    (xs x : Term) (s : native_String) (d : SmtDatatypeDecl) (i j : native_Nat) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) x) ≠
      SmtTerm.DtSel s d i j := by
  intro h
  cases xs <;> try cases h
  case Apply f tail =>
    cases f <;> try cases h
    case UOp op =>
      cases op <;> try cases h
      case _at__at_TypedList_nil =>
        exact eo_to_smt_set_insert_typed_nil_ne_dt_sel tail x s d i j (by
          change
            __eo_to_smt_set_insert
                (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) tail)
                (__eo_to_smt x) =
              SmtTerm.DtSel s d i j at h
          exact h)
    case Apply g head =>
      cases g <;> try cases h
      case UOp op =>
        cases op <;> cases h

private theorem eo_to_smt_set_insert_top_ne_dt_tester
    (xs x : Term) (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) x) ≠
      SmtTerm.DtTester s d i := by
  intro h
  cases xs <;> try cases h
  case Apply f tail =>
    cases f <;> try cases h
    case UOp op =>
      cases op <;> try cases h
      case _at__at_TypedList_nil =>
        exact eo_to_smt_set_insert_typed_nil_ne_dt_tester tail x s d i (by
          change
            __eo_to_smt_set_insert
                (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) tail)
                (__eo_to_smt x) =
              SmtTerm.DtTester s d i at h
          exact h)
    case Apply g head =>
      cases g <;> try cases h
      case UOp op =>
        cases op <;> cases h

private theorem eo_to_smt_set_insert_top_ne_dt_cons
    (xs x : Term) (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) x) ≠
      SmtTerm.DtCons s d i := by
  intro h
  cases xs <;> try cases h
  case Apply f tail =>
    cases f <;> try cases h
    case UOp op =>
      cases op <;> try cases h
      case _at__at_TypedList_nil =>
        exact eo_to_smt_set_insert_typed_nil_ne_dt_cons tail x s d i (by
          change
            __eo_to_smt_set_insert
                (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) tail)
                (__eo_to_smt x) =
              SmtTerm.DtCons s d i at h
          exact h)
    case Apply g head =>
      cases g <;> try cases h
      case UOp op =>
        cases op <;> cases h

private theorem eo_to_smt_exists_top_ne_dt_sel
    (xs body : Term) (s : native_String) (d : SmtDatatypeDecl) (i j : native_Nat) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body) ≠
      SmtTerm.DtSel s d i j := by
  intro h
  cases xs <;> try cases h
  case Apply f vs =>
    cases f <;> try cases h
    case Apply g v =>
      cases g <;> try cases h
      case __eo_List_cons =>
        cases v <;> try cases h
        case Var name T =>
          cases name <;> cases h

private theorem eo_to_smt_exists_top_ne_dt_tester
    (xs body : Term) (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body) ≠
      SmtTerm.DtTester s d i := by
  intro h
  cases xs <;> try cases h
  case Apply f vs =>
    cases f <;> try cases h
    case Apply g v =>
      cases g <;> try cases h
      case __eo_List_cons =>
        cases v <;> try cases h
        case Var name T =>
          cases name <;> cases h

private theorem eo_to_smt_exists_top_ne_dt_cons
    (xs body : Term) (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body) ≠
      SmtTerm.DtCons s d i := by
  intro h
  cases xs <;> try cases h
  case Apply f vs =>
    cases f <;> try cases h
    case Apply g v =>
      cases g <;> try cases h
      case __eo_List_cons =>
        cases v <;> try cases h
        case Var name T =>
          cases name <;> cases h

private theorem eo_to_smt_forall_top_ne_dt_sel
    (xs body : Term) (s : native_String) (d : SmtDatatypeDecl) (i j : native_Nat) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body) ≠
      SmtTerm.DtSel s d i j := by
  intro h
  cases xs <;> cases h

private theorem eo_to_smt_forall_top_ne_dt_tester
    (xs body : Term) (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body) ≠
      SmtTerm.DtTester s d i := by
  intro h
  cases xs <;> cases h

private theorem eo_to_smt_forall_top_ne_dt_cons
    (xs body : Term) (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body) ≠
      SmtTerm.DtCons s d i := by
  intro h
  cases xs <;> cases h

private theorem eo_to_smt_quant_skolemize_top_ne_dt_sel
    (q idx : Term) (s : native_String) (d : SmtDatatypeDecl) (i j : native_Nat) :
    __eo_to_smt (Term._at_quantifiers_skolemize q idx) ≠ SmtTerm.DtSel s d i j := by
  intro h
  cases q <;> try cases h
  case Apply f body =>
    cases f <;> try cases h
    case Apply g xs =>
      cases g <;> try cases h
      case UOp op =>
        cases op <;> try cases h
        case «forall» =>
          change native_ite (__eo_to_smt_nat_is_valid idx)
              (__eo_to_smt_quantifiers_skolemize
                xs (SmtTerm.not (__eo_to_smt body)) (__eo_to_smt_nat idx))
              SmtTerm.None =
            SmtTerm.DtSel s d i j at h
          unfold native_ite at h
          split at h <;> try cases h
          exact eo_to_smt_quant_skolemize_ne_dt_sel _ _ _ _ _ _ _ h

private theorem eo_to_smt_quant_skolemize_top_ne_dt_tester
    (q idx : Term) (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    __eo_to_smt (Term._at_quantifiers_skolemize q idx) ≠ SmtTerm.DtTester s d i := by
  intro h
  cases q <;> try cases h
  case Apply f body =>
    cases f <;> try cases h
    case Apply g xs =>
      cases g <;> try cases h
      case UOp op =>
        cases op <;> try cases h
        case «forall» =>
          change native_ite (__eo_to_smt_nat_is_valid idx)
              (__eo_to_smt_quantifiers_skolemize
                xs (SmtTerm.not (__eo_to_smt body)) (__eo_to_smt_nat idx))
              SmtTerm.None =
            SmtTerm.DtTester s d i at h
          unfold native_ite at h
          split at h <;> try cases h
          exact eo_to_smt_quant_skolemize_ne_dt_tester _ _ _ _ _ _ h

private theorem eo_to_smt_quant_skolemize_top_ne_dt_cons
    (q idx : Term) (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    __eo_to_smt (Term._at_quantifiers_skolemize q idx) ≠ SmtTerm.DtCons s d i := by
  intro h
  cases q <;> try cases h
  case Apply f body =>
    cases f <;> try cases h
    case Apply g xs =>
      cases g <;> try cases h
      case UOp op =>
        cases op <;> try cases h
        case «forall» =>
          change native_ite (__eo_to_smt_nat_is_valid idx)
              (__eo_to_smt_quantifiers_skolemize
                xs (SmtTerm.not (__eo_to_smt body)) (__eo_to_smt_nat idx))
              SmtTerm.None =
            SmtTerm.DtCons s d i at h
          unfold native_ite at h
          split at h <;> try cases h
          exact eo_to_smt_quant_skolemize_ne_dt_cons _ _ _ _ _ _ h

theorem eo_to_smt_apply_ne_dt_sel
    (f x : Term) (s : native_String) (d : SmtDatatypeDecl) (i j : native_Nat) :
    __eo_to_smt (Term.Apply f x) ≠ SmtTerm.DtSel s d i j := by
  intro h
  cases f <;> try cases h
  case UOp op =>
    cases op <;> try cases h
    case distinct =>
      exact eo_to_smt_distinct_top_ne_dt_sel x s d i j h
    case _at_bvsize =>
      change native_ite (native_zleq 0 (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))))
          (SmtTerm._at_purify
            (SmtTerm.Numeral (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x)))))
          SmtTerm.None =
        SmtTerm.DtSel s d i j at h
      unfold native_ite at h
      split at h <;> cases h
  case UOp1 op y =>
    cases op <;> try cases h
    case tuple_select =>
      exact eo_to_smt_tuple_select_ne_dt_sel _ _ _ _ _ _ _ h
  case UOp2 op y z =>
    cases op <;> try cases h
  case Apply g y =>
    cases g <;> try cases h
    case UOp1 op z =>
      cases op <;> try cases h
      case update =>
        exact eo_to_smt_updater_ne_dt_sel _ _ _ _ _ _ _ h
      case tuple_update =>
        exact eo_to_smt_tuple_update_ne_dt_sel _ _ _ _ _ _ _ _ h
    case UOp op =>
      cases op <;> try cases h
      case set_insert =>
        exact eo_to_smt_set_insert_top_ne_dt_sel _ _ _ _ _ _ h
      case «forall» =>
        exact eo_to_smt_forall_top_ne_dt_sel _ _ _ _ _ _ h
      case «exists» =>
        exact eo_to_smt_exists_top_ne_dt_sel _ _ _ _ _ _ h
      case tuple =>
        exact eo_to_smt_tuple_ne_dt_sel x y s d i j h
      case _at_array_deq_diff =>
        exact eo_to_smt_array_deq_diff_ne_dt_sel
          (__eo_to_smt y) (__eo_to_smt x) s d i j h
      case _at_sets_deq_diff =>
        exact eo_to_smt_sets_deq_diff_ne_dt_sel
          (__eo_to_smt y) (__eo_to_smt x) s d i j h
    case Apply k z =>
      cases k <;> try cases h
      case UOp op =>
        cases op <;> try cases h
      case Apply g w =>
        cases g <;> try cases h
        case UOp op =>
          cases op <;> cases h

theorem eo_to_smt_apply_ne_dt_tester
    (f x : Term) (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    __eo_to_smt (Term.Apply f x) ≠ SmtTerm.DtTester s d i := by
  intro h
  cases f <;> try cases h
  case UOp op =>
    cases op <;> try cases h
    case distinct =>
      exact eo_to_smt_distinct_top_ne_dt_tester x s d i h
    case _at_bvsize =>
      change native_ite (native_zleq 0 (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))))
          (SmtTerm._at_purify
            (SmtTerm.Numeral (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x)))))
          SmtTerm.None =
        SmtTerm.DtTester s d i at h
      unfold native_ite at h
      split at h <;> cases h
  case UOp1 op y =>
    cases op <;> try cases h
    case tuple_select =>
      exact eo_to_smt_tuple_select_ne_dt_tester _ _ _ _ _ _ h
  case UOp2 op y z =>
    cases op <;> try cases h
  case Apply g y =>
    cases g <;> try cases h
    case UOp1 op z =>
      cases op <;> try cases h
      case update =>
        exact eo_to_smt_updater_ne_dt_tester _ _ _ _ _ _ h
      case tuple_update =>
        exact eo_to_smt_tuple_update_ne_dt_tester _ _ _ _ _ _ _ h
    case UOp op =>
      cases op <;> try cases h
      case set_insert =>
        exact eo_to_smt_set_insert_top_ne_dt_tester _ _ _ _ _ h
      case «forall» =>
        exact eo_to_smt_forall_top_ne_dt_tester _ _ _ _ _ h
      case «exists» =>
        exact eo_to_smt_exists_top_ne_dt_tester _ _ _ _ _ h
      case tuple =>
        exact eo_to_smt_tuple_ne_dt_tester x y s d i h
      case _at_array_deq_diff =>
        exact eo_to_smt_array_deq_diff_ne_dt_tester
          (__eo_to_smt y) (__eo_to_smt x) s d i h
      case _at_sets_deq_diff =>
        exact eo_to_smt_sets_deq_diff_ne_dt_tester
          (__eo_to_smt y) (__eo_to_smt x) s d i h
    case Apply k z =>
      cases k <;> try cases h
      case UOp op =>
        cases op <;> try cases h
      case Apply g w =>
        cases g <;> try cases h
        case UOp op =>
          cases op <;> cases h

private theorem eo_to_smt_apply_ne_dt_cons
    (f x : Term) (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    __eo_to_smt (Term.Apply f x) ≠ SmtTerm.DtCons s d i := by
  intro h
  cases f <;> try cases h
  case UOp op =>
    cases op <;> try cases h
    case distinct =>
      exact eo_to_smt_distinct_top_ne_dt_cons x s d i h
    case _at_bvsize =>
      change native_ite (native_zleq 0 (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))))
          (SmtTerm._at_purify
            (SmtTerm.Numeral (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x)))))
          SmtTerm.None =
        SmtTerm.DtCons s d i at h
      unfold native_ite at h
      split at h <;> cases h
  case UOp1 op y =>
    cases op <;> try cases h
    case tuple_select =>
      exact eo_to_smt_tuple_select_ne_dt_cons _ _ _ _ _ _ h
  case UOp2 op y z =>
    cases op <;> try cases h
  case Apply g y =>
    cases g <;> try cases h
    case UOp1 op z =>
      cases op <;> try cases h
      case update =>
        exact eo_to_smt_updater_ne_dt_cons _ _ _ _ _ _ h
      case tuple_update =>
        exact eo_to_smt_tuple_update_ne_dt_cons _ _ _ _ _ _ _ h
    case UOp op =>
      cases op <;> try cases h
      case set_insert =>
        exact eo_to_smt_set_insert_top_ne_dt_cons _ _ _ _ _ h
      case «forall» =>
        exact eo_to_smt_forall_top_ne_dt_cons _ _ _ _ _ h
      case «exists» =>
        exact eo_to_smt_exists_top_ne_dt_cons _ _ _ _ _ h
      case tuple =>
        exact eo_to_smt_tuple_ne_dt_cons x y s d i h
      case _at_array_deq_diff =>
        exact eo_to_smt_array_deq_diff_ne_dt_cons
          (__eo_to_smt y) (__eo_to_smt x) s d i h
      case _at_sets_deq_diff =>
        exact eo_to_smt_sets_deq_diff_ne_dt_cons
          (__eo_to_smt y) (__eo_to_smt x) s d i h
    case Apply k z =>
      cases k <;> try cases h
      case UOp op =>
        cases op <;> try cases h
      case Apply g w =>
        cases g <;> try cases h
        case UOp op =>
          cases op <;> cases h

/-- Rewrites the typing equation for `bvnot`. -/
private theorem typeof_bvnot_eq
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.bvnot t) =
      __smtx_typeof_bv_op_1 (__smtx_typeof t) := by
  rw [__smtx_typeof.eq_def] <;> simp only

/-- Rewrites the typing equation for `bvcomp`. -/
private theorem typeof_bvcomp_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.bvcomp t1 t2) =
      __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) (SmtType.BitVec 1) := by
  rw [__smtx_typeof.eq_def] <;> simp only

/-- Rewrites the typing equation for `bvneg`. -/
private theorem typeof_bvneg_eq
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.bvneg t) =
      __smtx_typeof_bv_op_1 (__smtx_typeof t) := by
  rw [__smtx_typeof.eq_def] <;> simp only

/-- Rewrites the typing equation for `bvnego`. -/
private theorem typeof_bvnego_eq
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.bvnego t) =
      __smtx_typeof_bv_op_1_ret (__smtx_typeof t) SmtType.Bool := by
  rw [__smtx_typeof.eq_def] <;> simp only

/-- Rewrites the typing equation for `seq_unit`. -/
private theorem typeof_seq_unit_eq
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.seq_unit t) =
      __smtx_typeof_guard_wf (SmtType.Seq (__smtx_typeof t))
        (SmtType.Seq (__smtx_typeof t)) := by
  rw [__smtx_typeof.eq_def] <;> simp only

/-- Rewrites the typing equation for `set_empty`. -/
private theorem typeof_set_empty_eq
    (T : SmtType) :
    __smtx_typeof (SmtTerm.set_empty T) =
      __smtx_typeof_guard_wf (SmtType.Set T) (SmtType.Set T) := by
  rw [__smtx_typeof.eq_def] <;> simp only

/-- Rewrites the typing equation for `set_singleton`. -/
private theorem typeof_set_singleton_eq
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.set_singleton t) =
      __smtx_typeof_guard_wf (SmtType.Set (__smtx_typeof t))
        (SmtType.Set (__smtx_typeof t)) := by
  rw [__smtx_typeof.eq_def] <;> simp only

/-- Rewrites the typing equation for `exists`. -/
private theorem typeof_exists_eq
    (s : native_String) (T : SmtType) (t : SmtTerm) :
    __smtx_typeof (SmtTerm.exists s T t) =
      native_ite (native_Teq (__smtx_typeof t) SmtType.Bool)
        (__smtx_typeof_guard_wf T SmtType.Bool)
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only

/-- Rewrites the typing equation for `forall`. -/
private theorem typeof_forall_eq
    (s : native_String) (T : SmtType) (t : SmtTerm) :
    __smtx_typeof (SmtTerm.forall s T t) =
      native_ite (native_Teq (__smtx_typeof t) SmtType.Bool)
        (__smtx_typeof_guard_wf T SmtType.Bool)
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only

/-- Computes the type of applying `none`. -/
theorem typeof_apply_none_eq
    (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply SmtTerm.None x) = SmtType.None := by
  have hGeneric : generic_apply_type SmtTerm.None x := by
    exact generic_apply_type_of_non_special_head _ _
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
  rw [hGeneric, smtx_typeof_none]
  simp [__smtx_typeof_apply]

/-- Computes the type of applying a term whose head is itself `none`. -/
theorem typeof_apply_apply_none_head_eq
    (y x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None y) x) = SmtType.None := by
  have hGeneric : generic_apply_type (SmtTerm.Apply SmtTerm.None y) x := by
    exact generic_apply_type_of_non_special_head _ _
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
  rw [hGeneric, typeof_apply_none_eq y]
  simp [__smtx_typeof_apply]

/-- Computes the type of applying a term whose binary head starts from `none`. -/
private theorem typeof_apply_apply_apply_none_head_eq
    (z y x : SmtTerm) :
    __smtx_typeof
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None z) y) x) =
      SmtType.None := by
  have hGeneric :
      generic_apply_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None z) y) x := by
    exact generic_apply_type_of_non_special_head _ _
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
  rw [hGeneric, typeof_apply_apply_none_head_eq z y]
  simp [__smtx_typeof_apply]

/-- Computes the type of applying a term whose ternary head starts from `none`. -/
theorem typeof_apply_apply_apply_apply_none_head_eq
    (w z y x : SmtTerm) :
    __smtx_typeof
        (SmtTerm.Apply
          (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None w) z) y) x) =
      SmtType.None := by
  have hGeneric :
      generic_apply_type
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None w) z) y) x := by
    exact generic_apply_type_of_non_special_head _ _
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
  rw [hGeneric, typeof_apply_apply_apply_none_head_eq w z y]
  simp [__smtx_typeof_apply]

/-- Computes the type of a generic apply with a non-function head. -/
private theorem typeof_generic_apply_non_function_head_eq_none
    (f x : SmtTerm)
    (hGeneric : generic_apply_type f x)
    (hFun : ∀ A B, __smtx_typeof f ≠ SmtType.FunType A B)
    (hIFun : ∀ A B, __smtx_typeof f ≠ SmtType.FunType A B)
    (hDtc : ∀ A B, __smtx_typeof f ≠ SmtType.DtcAppType A B) :
    __smtx_typeof (SmtTerm.Apply f x) = SmtType.None := by
  have _ := hIFun
  rw [hGeneric]
  cases hF : __smtx_typeof f <;> try rfl
  · exact False.elim (hFun _ _ hF)
  · exact False.elim (hDtc _ _ hF)

/-- Computes the type of applying a Boolean literal as a head. -/
private theorem typeof_apply_boolean_head_eq_none
    (b : native_Bool) (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.Boolean b) x) = SmtType.None := by
  exact typeof_generic_apply_non_function_head_eq_none _ _
    (generic_apply_type_of_non_special_head _ _
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h))
    (by intro A B h; rw [__smtx_typeof.eq_1] at h; cases h)
    (by intro A B h; rw [__smtx_typeof.eq_1] at h; cases h)
    (by intro A B h; rw [__smtx_typeof.eq_1] at h; cases h)

/-- Computes the type of applying an integer literal as a head. -/
private theorem typeof_apply_numeral_head_eq_none
    (n : native_Int) (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.Numeral n) x) = SmtType.None := by
  exact typeof_generic_apply_non_function_head_eq_none _ _
    (generic_apply_type_of_non_special_head _ _
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h))
    (by intro A B h; rw [__smtx_typeof.eq_2] at h; cases h)
    (by intro A B h; rw [__smtx_typeof.eq_2] at h; cases h)
    (by intro A B h; rw [__smtx_typeof.eq_2] at h; cases h)

/-- Computes the type of applying a rational literal as a head. -/
private theorem typeof_apply_rational_head_eq_none
    (r : native_Rat) (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.Rational r) x) = SmtType.None := by
  exact typeof_generic_apply_non_function_head_eq_none _ _
    (generic_apply_type_of_non_special_head _ _
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h))
    (by intro A B h; rw [__smtx_typeof.eq_3] at h; cases h)
    (by intro A B h; rw [__smtx_typeof.eq_3] at h; cases h)
    (by intro A B h; rw [__smtx_typeof.eq_3] at h; cases h)

/-- Computes the type of applying a string literal as a head. -/
private theorem typeof_apply_string_head_eq_none
    (s : native_String) (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.String s) x) = SmtType.None := by
  exact typeof_generic_apply_non_function_head_eq_none _ _
    (generic_apply_type_of_non_special_head _ _
      (by intro s' d i j h; cases h)
      (by intro s' d i h; cases h))
    (by
      intro A B h
      rw [__smtx_typeof.eq_4] at h
      cases hValid : native_string_valid s <;>
        simp [native_ite, hValid] at h)
    (by
      intro A B h
      rw [__smtx_typeof.eq_4] at h
      cases hValid : native_string_valid s <;>
        simp [native_ite, hValid] at h)
    (by
      intro A B h
      rw [__smtx_typeof.eq_4] at h
      cases hValid : native_string_valid s <;>
        simp [native_ite, hValid] at h)

/-- Computes the type of applying a bit-vector literal as a head. -/
private theorem typeof_apply_binary_head_eq_none
    (w n : native_Int) (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.Binary w n) x) = SmtType.None := by
  exact typeof_generic_apply_non_function_head_eq_none _ _
    (generic_apply_type_of_non_special_head _ _
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h))
    (by
      intro A B h
      rw [__smtx_typeof.eq_5] at h
      cases hCond :
          native_and (native_zleq 0 w) (native_zeq n (native_mod_total n (native_int_pow2 w))) <;>
        simp [native_ite, hCond] at h)
    (by
      intro A B h
      rw [__smtx_typeof.eq_5] at h
      cases hCond :
          native_and (native_zleq 0 w) (native_zeq n (native_mod_total n (native_int_pow2 w))) <;>
        simp [native_ite, hCond] at h)
    (by
      intro A B h
      rw [__smtx_typeof.eq_5] at h
      cases hCond :
          native_and (native_zleq 0 w) (native_zeq n (native_mod_total n (native_int_pow2 w))) <;>
        simp [native_ite, hCond] at h)

/-- Rewrites the typing equation for unary arithmetic negation. -/
private theorem typeof_uneg_eq
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.uneg t) =
      __smtx_typeof_arith_overload_op_1 (__smtx_typeof t) := by
  rw [__smtx_typeof.eq_25]

/-- Computes the type of applying a regular-language constant as a head. -/
private theorem typeof_apply_reglan_head_eq_none
    (f x : SmtTerm)
    (hF : __smtx_typeof f = SmtType.RegLan)
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i) :
    __smtx_typeof (SmtTerm.Apply f x) = SmtType.None := by
  have hGeneric : generic_apply_type f x :=
    generic_apply_type_of_non_special_head f x hSel hTester
  rw [hGeneric, hF]
  rfl

/-- Computes the type of applying the nullary tuple constructor as a head. -/
private theorem typeof_apply_tuple_unit_eq_none
    (x : SmtTerm) :
    __smtx_typeof
        (SmtTerm.Apply
          (SmtTerm.DtCons (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl
              (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)) 0) x) =
      SmtType.None := by
  have hGeneric :
      generic_apply_type
        (SmtTerm.DtCons (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl
            (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)) 0) x :=
    generic_apply_type_of_non_special_head _ _
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
  rw [hGeneric]
  simp [__eo_to_smt_tuple_decl, smtx_typeof_tuple_unit_translation]
  rfl

/-- Computes `__smtx_typeof_apply` for translated `seq_empty`. -/
theorem smtx_typeof_apply_eo_to_smt_seq_empty_eq_none
    (T X : SmtType) :
    __smtx_typeof_apply (__smtx_typeof (__eo_to_smt_seq_empty T)) X = SmtType.None := by
  cases T with
  | None
  | Bool
  | Int
  | Real
  | RegLan
  | BitVec _
  | Set _
  | Char
  | Datatype _ _
  | TypeRef _
  | USort _
  | Map _ _
  | FunType _ _
  | DtcAppType _ _ =>
      simp [__eo_to_smt_seq_empty, __smtx_typeof_apply]
  | Seq U =>
      rw [show __smtx_typeof (__eo_to_smt_seq_empty (SmtType.Seq U)) =
          __smtx_typeof_guard_wf (SmtType.Seq U) (SmtType.Seq U) by
        simp [__eo_to_smt_seq_empty, __smtx_typeof]]
      cases hWf : __smtx_type_wf (SmtType.Seq U) <;>
        simp [__smtx_typeof_apply, __smtx_typeof_guard_wf, native_ite, hWf]

/-- Computes the type of applying a translated `seq_empty` as a head. -/
theorem typeof_apply_eo_to_smt_seq_empty_eq_none
    (T : SmtType) (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (__eo_to_smt_seq_empty T) x) = SmtType.None := by
  have hGeneric : generic_apply_type (__eo_to_smt_seq_empty T) x := by
    cases T <;> simp [__eo_to_smt_seq_empty]
    all_goals
      exact generic_apply_type_of_non_special_head _ _
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
  rw [hGeneric]
  exact smtx_typeof_apply_eo_to_smt_seq_empty_eq_none T (__smtx_typeof x)

/-- Computes the type of applying a translated `set_empty` as a head. -/
theorem typeof_apply_eo_to_smt_set_empty_eq_none
    (T : SmtType) (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (__eo_to_smt_set_empty T) x) = SmtType.None := by
  cases T <;> simp [__eo_to_smt_set_empty]
  case Set U =>
    exact typeof_generic_apply_non_function_head_eq_none _ _
      (generic_apply_type_of_non_special_head _ _
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h))
      (by
        intro A B hFun
        have hNN : __smtx_typeof (SmtTerm.set_empty U) ≠ SmtType.None := by
          rw [hFun]
          simp
        have hTy := smtx_typeof_set_empty_of_non_none U hNN
        rw [hTy] at hFun
        cases hFun)
      (by
        intro A B hIFun
        have hNN : __smtx_typeof (SmtTerm.set_empty U) ≠ SmtType.None := by
          rw [hIFun]
          simp
        have hTy := smtx_typeof_set_empty_of_non_none U hNN
        rw [hTy] at hIFun
        cases hIFun)
      (by
        intro A B hDtc
        have hNN : __smtx_typeof (SmtTerm.set_empty U) ≠ SmtType.None := by
          rw [hDtc]
          simp
        have hTy := smtx_typeof_set_empty_of_non_none U hNN
        rw [hTy] at hDtc
        cases hDtc)
  all_goals exact typeof_apply_none_eq x

/-- Applying a zero-index integer `choice_nth` as a function is ill-typed. -/
theorem typeof_apply_choice_nth_int_eq_none
    (body x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.choice (native_string_lit "@x") SmtType.Int body) x) =
      SmtType.None := by
  exact typeof_generic_apply_non_function_head_eq_none _ _
    (generic_apply_type_of_non_special_head _ _
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h))
    (by
      intro A B hFun
      have hNN : term_has_non_none_type (SmtTerm.choice (native_string_lit "@x") SmtType.Int body) := by
        unfold term_has_non_none_type
        rw [hFun]
        simp
      have hTy := choice_term_typeof_of_non_none hNN
      rw [hTy] at hFun
      cases hFun)
    (by
      intro A B hIFun
      have hNN : term_has_non_none_type (SmtTerm.choice (native_string_lit "@x") SmtType.Int body) := by
        unfold term_has_non_none_type
        rw [hIFun]
        simp
      have hTy := choice_term_typeof_of_non_none hNN
      rw [hTy] at hIFun
      cases hIFun)
    (by
      intro A B hDtc
      have hNN : term_has_non_none_type (SmtTerm.choice (native_string_lit "@x") SmtType.Int body) := by
        unfold term_has_non_none_type
        rw [hDtc]
        simp
      have hTy := choice_term_typeof_of_non_none hNN
      rw [hTy] at hDtc
      cases hDtc)

/-- A non-`None` `str.indexof_re` term has integer type. -/
theorem smtx_typeof_str_indexof_re_of_non_none
    (s r n : SmtTerm)
    (hNN : term_has_non_none_type (SmtTerm.str_indexof_re s r n)) :
    __smtx_typeof (SmtTerm.str_indexof_re s r n) = SmtType.Int := by
  have hArgs := str_indexof_re_args_of_non_none hNN
  rw [typeof_str_indexof_re_eq s r n, hArgs.1, hArgs.2.1, hArgs.2.2]
  simp [native_ite, native_Teq]

/-- Applying a `str.indexof_re` result as a function is ill-typed. -/
theorem typeof_apply_str_indexof_re_head_eq_none
    (s r n x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.str_indexof_re s r n) x) =
      SmtType.None := by
  exact typeof_generic_apply_non_function_head_eq_none _ _
    (generic_apply_type_of_non_special_head _ _
      (by intro s' d i j h; cases h)
      (by intro s' d i h; cases h))
    (by
      intro A B hFun
      have hNN : term_has_non_none_type (SmtTerm.str_indexof_re s r n) := by
        unfold term_has_non_none_type
        rw [hFun]
        simp
      have hTy := smtx_typeof_str_indexof_re_of_non_none s r n hNN
      rw [hTy] at hFun
      cases hFun)
    (by
      intro A B hIFun
      have hNN : term_has_non_none_type (SmtTerm.str_indexof_re s r n) := by
        unfold term_has_non_none_type
        rw [hIFun]
        simp
      have hTy := smtx_typeof_str_indexof_re_of_non_none s r n hNN
      rw [hTy] at hIFun
      cases hIFun)
    (by
      intro A B hDtc
      have hNN : term_has_non_none_type (SmtTerm.str_indexof_re s r n) := by
        unfold term_has_non_none_type
        rw [hDtc]
        simp
      have hTy := smtx_typeof_str_indexof_re_of_non_none s r n hNN
      rw [hTy] at hDtc
      cases hDtc)

/-- Closes branches whose SMT translation is already typed as `none`. -/
private theorem eo_to_smt_typeof_matches_translation_of_smt_none
    (t : Term)
    (hNone : __smtx_typeof (__eo_to_smt t) = SmtType.None) :
    __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t) := by
  intro hNonNone
  exact False.elim (hNonNone hNone)

/-- Rewrites the typing equation for rationals. -/
private theorem typeof_rational_eq
    (q : native_Rat) :
    __smtx_typeof (SmtTerm.Rational q) = SmtType.Real := by
  unfold __smtx_typeof
  rfl

/-- Computes the type of the one-bit literal used by `bvite`. -/
private theorem typeof_binary_one_eq :
    __smtx_typeof (SmtTerm.Binary 1 1) = SmtType.BitVec 1 := by
  have hNN : __smtx_typeof (SmtTerm.Binary 1 1) ≠ SmtType.None := by
    unfold __smtx_typeof
    simp [native_ite, SmtEval.native_and, native_zleq, native_zeq, native_mod_total,
      native_int_pow2]
    native_decide
  simpa [native_int_to_nat, SmtEval.native_int_to_nat] using
    smtx_typeof_binary_of_non_none 1 1 hNN

private theorem eo_to_smt_type_injective_of_type_wf_rec
    {T U : Term} {A : SmtType}
    (hT : __eo_to_smt_type T = A)
    (hU : __eo_to_smt_type U = A)
    (hWF : __smtx_type_wf_rec A = true) :
    T = U := by
  exact eo_to_smt_type_injective_of_field_wf_rec hT hU
    (smtx_type_field_wf_rec_of_type_wf_rec (refs := native_reflist_nil) hWF)

/--
EO-side application typing for function-like SMT heads.

The key extra hypothesis is field well-formedness of the argument type.  That
is the bit needed to turn equality of translated SMT types into syntactic EO
type equality, avoiding the previous circular appeal to the whole translation
theorem.
-/
private theorem eo_to_smt_type_typeof_apply_from_ih_of_fun_like
    (f x : Term) (A B : SmtType) {refs : RefList}
    (ihF :
      __smtx_typeof (__eo_to_smt f) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt f) = __eo_to_smt_type (__eo_typeof f))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hHead :
      __smtx_typeof (__eo_to_smt f) = SmtType.FunType A B ∨
        __smtx_typeof (__eo_to_smt f) = SmtType.DtcAppType A B)
    (hX : __smtx_typeof (__eo_to_smt x) = A)
    (hEoApply :
      __eo_typeof (Term.Apply f x) =
        __eo_typeof_apply (__eo_typeof f) (__eo_typeof x))
    (hArgWF : smtx_type_field_wf_rec A refs)
    (hA : A ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply f x)) = B := by
  have hFNN : __smtx_typeof (__eo_to_smt f) ≠ SmtType.None := by
    rcases hHead with hHead | hHead
    · rw [hHead]
      simp
    · rw [hHead]
      simp
  have hXTrans : __eo_to_smt_type (__eo_typeof x) = A :=
    eo_to_smt_type_typeof_of_smt_type_from_ih x ihX hX hA
  rcases hHead with hHead | hHead
  · have hFTrans : __eo_to_smt_type (__eo_typeof f) = SmtType.FunType A B := by
      rw [← ihF hFNN]
      exact hHead
    rcases eo_to_smt_type_eq_fun hFTrans with ⟨U, V, hFEq, hU, hV⟩
    have hxEo : __eo_typeof x = U :=
      eo_to_smt_type_injective_of_field_wf_rec hXTrans hU hArgWF
    have hUNonNone : __eo_to_smt_type U ≠ SmtType.None := by
      rw [hU]
      exact hA
    exact
      (eo_to_smt_type_typeof_apply_of_fun_like
        x f U V
        hEoApply
        (Or.inl hFEq)
        hxEo hUNonNone).trans hV
  · have hFTrans : __eo_to_smt_type (__eo_typeof f) = SmtType.DtcAppType A B := by
      rw [← ihF hFNN]
      exact hHead
    rcases eo_to_smt_type_eq_dtc_app hFTrans with ⟨U, V, hFEq, hU, hV⟩
    have hxEo : __eo_typeof x = U :=
      eo_to_smt_type_injective_of_field_wf_rec hXTrans hU hArgWF
    have hUNonNone : __eo_to_smt_type U ≠ SmtType.None := by
      rw [hU]
      exact hA
    exact
      (eo_to_smt_type_typeof_apply_of_fun_like
        x f U V
        hEoApply
        (Or.inr hFEq)
        hxEo hUNonNone).trans hV

/-- A `choice` function-like type has a well-formed argument field. -/
private theorem choice_nth_fun_like_arg_field_wf
    (s : native_String) (T : SmtType) (body : SmtTerm) {A B : SmtType}
    (hHead :
      __smtx_typeof (SmtTerm.choice s T body) = SmtType.FunType A B ∨
        __smtx_typeof (SmtTerm.choice s T body) = SmtType.DtcAppType A B) :
    smtx_type_field_wf_rec A native_reflist_nil := by
  have hNN : term_has_non_none_type (SmtTerm.choice s T body) := by
    unfold term_has_non_none_type
    rcases hHead with hHead | hHead
    · rw [hHead]
      simp
    · rw [hHead]
      simp
  have hGuard :
      __smtx_typeof (SmtTerm.choice s T body) =
        __smtx_typeof_guard_wf T T :=
    Smtm.choice_term_guard_type_of_non_none hNN
  have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    intro hNone
    exact hNN (by rw [hGuard, hNone])
  have hTWF : __smtx_type_wf T = true :=
    Smtm.smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
  have hChoiceTy : __smtx_typeof (SmtTerm.choice s T body) = T :=
    Smtm.choice_term_typeof_of_non_none hNN
  rcases hHead with hHead | hHead
  · have hTFun : T = SmtType.FunType A B := hChoiceTy.symm.trans hHead
    have hTWF' : __smtx_type_wf (SmtType.FunType A B) = true := by
      simpa [hTFun] using hTWF
    exact smtx_type_field_wf_rec_of_type_wf_rec
      (fun_type_wf_rec_components_of_wf hTWF').1
  · have hTDtc : T = SmtType.DtcAppType A B := hChoiceTy.symm.trans hHead
    have hBad := hTWF
    rw [hTDtc] at hBad
    simp [__smtx_type_wf, __smtx_type_wf_rec, native_and] at hBad

/-- Skolemization is always a `choice` at the head or `none`, so function-like
    results have well-formed arguments. -/
private theorem eo_to_smt_quantifiers_skolemize_fun_like_arg_field_wf
    (vs : Term) (G : SmtTerm) (n : native_Nat) {A B : SmtType}
    (hHead :
      __smtx_typeof (__eo_to_smt_quantifiers_skolemize vs G n) = SmtType.FunType A B ∨
        __smtx_typeof (__eo_to_smt_quantifiers_skolemize vs G n) = SmtType.DtcAppType A B) :
    smtx_type_field_wf_rec A native_reflist_nil := by
  revert hHead
  induction n generalizing vs G with
  | zero =>
      intro hHead
      unfold __eo_to_smt_quantifiers_skolemize at hHead
      split at hHead <;>
        first
        | exact choice_nth_fun_like_arg_field_wf _ _ _ hHead
        | simp_all
  | succ n ih =>
      intro hHead
      unfold __eo_to_smt_quantifiers_skolemize at hHead
      split at hHead <;> (try subst_eqs) <;>
        first
        | exact ih _ _ hHead
        | (exfalso; simp_all)

private theorem smtx_typeof_none_not_fun_like
    {A B : SmtType}
    (hHead :
      __smtx_typeof SmtTerm.None = SmtType.FunType A B ∨
        __smtx_typeof SmtTerm.None = SmtType.DtcAppType A B) :
    False := by
  rcases hHead with hHead | hHead
  · rw [smtx_typeof_none] at hHead
    cases hHead
  · rw [smtx_typeof_none] at hHead
    cases hHead

private theorem eo_to_smt_none_not_fun_like
    {t : Term} {A B : SmtType}
    (hNone : __eo_to_smt t = SmtTerm.None)
    (hHead :
      __smtx_typeof (__eo_to_smt t) = SmtType.FunType A B ∨
        __smtx_typeof (__eo_to_smt t) = SmtType.DtcAppType A B) :
    False := by
  rw [hNone] at hHead
  exact smtx_typeof_none_not_fun_like hHead

private theorem eo_to_smt_quant_skolemize_top_non_forall_none
    {op : UserOp} (h : op ≠ UserOp.forall) (xs body idx : Term) :
    __eo_to_smt
        (Term._at_quantifiers_skolemize
          (Term.Apply (Term.Apply (Term.UOp op) xs) body) idx) =
      SmtTerm.None := by
  cases op <;> first | rfl | exact False.elim (h rfl)

/--
Top-level `_at_quantifiers_skolemize` only produces a function-like SMT term
through the inner skolemization helper, whose arguments are already known to be
field-well-formed.
-/
private theorem eo_to_smt_quantifiers_skolemize_top_fun_like_arg_field_wf
    (q idx : Term) {A B : SmtType}
    (hHead :
      __smtx_typeof (__eo_to_smt (Term._at_quantifiers_skolemize q idx)) =
          SmtType.FunType A B ∨
        __smtx_typeof (__eo_to_smt (Term._at_quantifiers_skolemize q idx)) =
          SmtType.DtcAppType A B) :
    smtx_type_field_wf_rec A native_reflist_nil := by
  cases q
  case Apply f body =>
    cases f
    case Apply g xs =>
      cases g
      case UOp op =>
        by_cases hForall : op = UserOp.forall
        · subst op
          have hHead' :
              __smtx_typeof
                  (native_ite (__eo_to_smt_nat_is_valid idx)
                    (__eo_to_smt_quantifiers_skolemize
                      xs (SmtTerm.not (__eo_to_smt body))
                      (__eo_to_smt_nat idx))
                    SmtTerm.None) =
                    SmtType.FunType A B ∨
                __smtx_typeof
                  (native_ite (__eo_to_smt_nat_is_valid idx)
                    (__eo_to_smt_quantifiers_skolemize
                      xs (SmtTerm.not (__eo_to_smt body))
                      (__eo_to_smt_nat idx))
                    SmtTerm.None) =
                    SmtType.DtcAppType A B := by
            change
              __smtx_typeof
                  (native_ite (__eo_to_smt_nat_is_valid idx)
                    (__eo_to_smt_quantifiers_skolemize
                      xs (SmtTerm.not (__eo_to_smt body))
                      (__eo_to_smt_nat idx))
                    SmtTerm.None) =
                    SmtType.FunType A B ∨
                __smtx_typeof
                  (native_ite (__eo_to_smt_nat_is_valid idx)
                    (__eo_to_smt_quantifiers_skolemize
                      xs (SmtTerm.not (__eo_to_smt body))
                      (__eo_to_smt_nat idx))
                    SmtTerm.None) =
                    SmtType.DtcAppType A B at hHead
            exact hHead
          unfold native_ite at hHead'
          split at hHead'
          · exact
              eo_to_smt_quantifiers_skolemize_fun_like_arg_field_wf
                xs (SmtTerm.not (__eo_to_smt body))
                (__eo_to_smt_nat idx) hHead'
          · exact False.elim (smtx_typeof_none_not_fun_like hHead')
        · exact False.elim
            (eo_to_smt_none_not_fun_like
              (eo_to_smt_quant_skolemize_top_non_forall_none hForall xs body idx)
              hHead)
      all_goals
        exact False.elim (eo_to_smt_none_not_fun_like (by rfl) hHead)
    all_goals
      exact False.elim (eo_to_smt_none_not_fun_like (by rfl) hHead)
  all_goals
    exact False.elim (eo_to_smt_none_not_fun_like (by rfl) hHead)

private theorem smtx_seq_component_field_wf_rec_of_non_none_type_apply
    (x : SmtTerm) (T : SmtType)
    (hxTy : __smtx_typeof x = SmtType.Seq T) :
    smtx_type_field_wf_rec T native_reflist_nil :=
  smtx_type_field_wf_rec_of_type_wf_rec
    (smt_seq_component_wf_rec_of_non_none_type x T hxTy)

private theorem smtx_set_component_field_wf_rec_of_non_none_type_apply
    (x : SmtTerm) (T : SmtType)
    (hxTy : __smtx_typeof x = SmtType.Set T) :
    smtx_type_field_wf_rec T native_reflist_nil :=
  smtx_type_field_wf_rec_of_type_wf_rec
    (smt_set_component_wf_rec_of_non_none_type x T hxTy)

private theorem smtx_map_components_field_wf_rec_of_non_none_type_apply
    (x : SmtTerm) (A B : SmtType)
    (hxTy : __smtx_typeof x = SmtType.Map A B) :
    smtx_type_field_wf_rec A native_reflist_nil ∧
      smtx_type_field_wf_rec B native_reflist_nil := by
  have hComps := smt_map_components_wf_rec_of_non_none_type x A B hxTy
  exact ⟨smtx_type_field_wf_rec_of_type_wf_rec hComps.1,
    smtx_type_field_wf_rec_of_type_wf_rec hComps.2⟩

private theorem smtx_fun_components_field_wf_rec_of_non_none_type_apply
    (x : SmtTerm) (A B : SmtType)
    (hxTy : __smtx_typeof x = SmtType.FunType A B) :
    smtx_type_field_wf_rec A native_reflist_nil ∧
      __smtx_type_wf B = true := by
  have hComps := smt_fun_components_wf_rec_of_non_none_type x A B hxTy
  exact ⟨smtx_type_field_wf_rec_of_type_wf_rec hComps.1, hComps.2⟩

private theorem smtx_datatype_field_wf_rec_of_non_none_type_apply
    (x : SmtTerm) (s : native_String) (d : SmtDatatypeDecl)
    (hxTy : __smtx_typeof x = SmtType.Datatype s d) :
  smtx_type_field_wf_rec (SmtType.Datatype s d) native_reflist_nil :=
  smtx_type_field_wf_rec_of_type_wf_rec
    (smtx_type_wf_rec_of_type_wf (by simp)
      (by intro A B h; cases h)
      (by intro A B h; cases h)
      (smt_datatype_wf_of_non_none_type x s d hxTy))

private theorem eo_typeof_eq_map_of_smt_map_from_ih
    (t : Term)
    (ih :
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t))
    {A B : SmtType}
    (h : __smtx_typeof (__eo_to_smt t) = SmtType.Map A B) :
    ∃ U V, __eo_typeof t = Term.Apply (Term.Apply (Term.UOp UserOp.Array) U) V ∧
      __eo_to_smt_type U = A ∧ __eo_to_smt_type V = B := by
  exact eo_to_smt_type_eq_map
    (eo_to_smt_type_typeof_of_smt_type_from_ih t ih h (by simp))

/-- Simplifies EO-to-SMT translation for sequence binary operators returning a sequence. -/
private theorem eo_to_smt_typeof_matches_translation_apply_seq_binop
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (x y : Term)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x) =
        smtOp (__eo_to_smt y) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_seq_op_2
          (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x)))
    (hEo :
      ∀ {T : Term},
        __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) T ->
        __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) T ->
        __eo_to_smt_type T ≠ SmtType.None ->
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
          __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) := by
  have hApplyNN :
      term_has_non_none_type (smtOp (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases seq_binop_args_of_non_none (op := smtOp) hTy hApplyNN with ⟨T, hY, hX⟩
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
        SmtType.Seq T := by
    rw [hTranslate, hTy, hY, hX]
    simp [__smtx_typeof_seq_op_2, native_ite, native_Teq]
  have hTWF :
      smtx_type_field_wf_rec T native_reflist_nil :=
    smtx_seq_component_field_wf_rec_of_non_none_type_apply (__eo_to_smt y) T hY
  have hTNN : T ≠ SmtType.None := by
    intro hNone
    subst T
    simp [smtx_type_field_wf_rec, __smtx_type_wf_rec] at hTWF
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih y ihY hY with ⟨U, hYU, hU⟩
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih x ihX hX with ⟨V, hXV, hV⟩
  have hVU : V = U :=
    eo_to_smt_type_injective_of_field_wf_rec hV hU hTWF
  have hXU : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) U := by
    rw [hXV, hVU]
  have hEoTy :
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
        SmtType.Seq T := by
    have hSeqU :
        __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U) = SmtType.Seq T := by
      simp [__eo_to_smt_type, hU,
        smtx_typeof_guard_of_non_none T (SmtType.Seq T) hTNN]
    exact (hEo (T := U) hYU hXU (by rw [hU]; exact hTNN)).trans hSeqU
  exact hSmt.trans hEoTy.symm

/-- Simplifies EO-to-SMT translation for sequence binary operators returning a fixed type. -/
private theorem eo_to_smt_typeof_matches_translation_apply_seq_ret_binop
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (ret : SmtType) (x y : Term)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x) =
        smtOp (__eo_to_smt y) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_seq_op_2_ret
          (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x)) ret)
    (hEo :
      ∀ {T : Term},
        __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) T ->
        __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) T ->
        __eo_to_smt_type T ≠ SmtType.None ->
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
          ret)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) := by
  have hApplyNN :
      term_has_non_none_type (smtOp (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases seq_binop_args_of_non_none_ret (op := smtOp) (R := ret) hTy hApplyNN with
    ⟨T, hY, hX⟩
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
        ret := by
    rw [hTranslate, hTy, hY, hX]
    simp [__smtx_typeof_seq_op_2_ret, native_ite, native_Teq]
  have hTWF :
      smtx_type_field_wf_rec T native_reflist_nil :=
    smtx_seq_component_field_wf_rec_of_non_none_type_apply (__eo_to_smt y) T hY
  have hTNN : T ≠ SmtType.None := by
    intro hNone
    subst T
    simp [smtx_type_field_wf_rec, __smtx_type_wf_rec] at hTWF
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih y ihY hY with ⟨U, hYU, hU⟩
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih x ihX hX with ⟨V, hXV, hV⟩
  have hVU : V = U :=
    eo_to_smt_type_injective_of_field_wf_rec hV hU hTWF
  have hXU : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) U := by
    rw [hXV, hVU]
  have hEoTy :
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
        ret :=
    hEo (T := U) hYU hXU (by rw [hU]; exact hTNN)
  exact hSmt.trans hEoTy.symm

/-- Simplifies EO-to-SMT translation for sequence-char binary operators. -/
private theorem eo_to_smt_typeof_matches_translation_apply_seq_char_binop
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (ret : SmtType) (x y : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x) =
        smtOp (__eo_to_smt y) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt y) (__eo_to_smt x)) =
        native_ite (native_Teq (__smtx_typeof (__eo_to_smt y)) (SmtType.Seq SmtType.Char))
          (native_ite (native_Teq (__smtx_typeof (__eo_to_smt x)) (SmtType.Seq SmtType.Char))
            ret SmtType.None)
          SmtType.None)
    (hEo :
      __smtx_typeof (__eo_to_smt y) = SmtType.Seq SmtType.Char ->
      __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char ->
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
        ret)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) := by
  have hApplyNN :
      term_has_non_none_type (smtOp (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  have hArgs := seq_char_binop_args_of_non_none (op := smtOp) hTy hApplyNN
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
        ret := by
    rw [hTranslate, hTy]
    simp [hArgs.1, hArgs.2, native_ite, native_Teq]
  exact hSmt.trans (hEo hArgs.1 hArgs.2).symm

/-- Simplifies EO-to-SMT translation for regular-language binary operators. -/
private theorem eo_to_smt_typeof_matches_translation_apply_reglan_binop
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (x y : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x) =
        smtOp (__eo_to_smt y) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt y) (__eo_to_smt x)) =
        native_ite (native_Teq (__smtx_typeof (__eo_to_smt y)) SmtType.RegLan)
          (native_ite (native_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.RegLan)
            SmtType.RegLan SmtType.None)
          SmtType.None)
    (hEo :
      __smtx_typeof (__eo_to_smt y) = SmtType.RegLan ->
      __smtx_typeof (__eo_to_smt x) = SmtType.RegLan ->
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
        SmtType.RegLan)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) := by
  have hApplyNN :
      term_has_non_none_type (smtOp (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  have hArgs := reglan_binop_args_of_non_none (op := smtOp) hTy hApplyNN
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
        SmtType.RegLan := by
    rw [hTranslate, hTy]
    simp [hArgs.1, hArgs.2, native_ite, native_Teq]
  exact hSmt.trans (hEo hArgs.1 hArgs.2).symm

/-- Simplifies EO-to-SMT translation for sequence-char/regular-language binary operators. -/
private theorem eo_to_smt_typeof_matches_translation_apply_seq_char_reglan_binop
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (ret : SmtType) (x y : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x) =
        smtOp (__eo_to_smt y) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt y) (__eo_to_smt x)) =
        native_ite (native_Teq (__smtx_typeof (__eo_to_smt y)) (SmtType.Seq SmtType.Char))
          (native_ite (native_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.RegLan)
            ret SmtType.None)
          SmtType.None)
    (hEo :
      __smtx_typeof (__eo_to_smt y) = SmtType.Seq SmtType.Char ->
      __smtx_typeof (__eo_to_smt x) = SmtType.RegLan ->
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
        ret)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) := by
  have hApplyNN :
      term_has_non_none_type (smtOp (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  have hArgs := seq_char_reglan_args_of_non_none (op := smtOp) hTy hApplyNN
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
        ret := by
    rw [hTranslate, hTy]
    simp [hArgs.1, hArgs.2, native_ite, native_Teq]
  exact hSmt.trans (hEo hArgs.1 hArgs.2).symm

/-
The old datatype-body substitution development below predates
`SmtDatatypeDecl`.  Datatype references are now resolved through a declaration
environment, so none of these private substitution lemmas describe the current
SMT model.  The live translation proof no longer depends on this block.

private def reflist_equiv_apply (xs ys : RefList) : Prop :=
  ∀ s, native_reflist_contains xs s = native_reflist_contains ys s

def smtx_type_substitute_top_apply (sub : native_String) (d0 : SmtDatatype) :
    SmtType -> SmtType
  | SmtType.Datatype s2 d2 =>
      SmtType.Datatype s2
        (native_ite (native_streq sub s2) d2
          (__smtx_dt_substitute sub (__smtx_dt_lift s2 d2 d0) d2))
  | SmtType.TypeRef s2 =>
      native_ite (native_streq sub s2) (SmtType.Datatype sub d0) (SmtType.TypeRef s2)
  | T => T

@[simp] private theorem smtx_type_substitute_top_apply_eq_smtx_type_substitute
    (sub : native_String) (d0 : SmtDatatype) (T : SmtType) :
    __smtx_type_substitute sub d0 T =
      smtx_type_substitute_top_apply sub d0 T := by
  cases T <;> simp [__smtx_type_substitute, smtx_type_substitute_top_apply]

private def smtx_chain_type_substitute_top_apply
    (sub : native_String) (d0 : SmtDatatype) : SmtType -> SmtType
  | SmtType.DtcAppType A B =>
      SmtType.DtcAppType
        (smtx_chain_type_substitute_top_apply sub d0 A)
        (smtx_chain_type_substitute_top_apply sub d0 B)
  | T => smtx_type_substitute_top_apply sub d0 T

@[simp] private theorem native_Teq_typeRef_typeRef_apply
    (s t : native_String) :
    native_Teq (SmtType.TypeRef s) (SmtType.TypeRef t) = native_streq s t := by
  simp [native_Teq, native_streq]

mutual

private def smtx_type_context_substitute_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype)
    (doSub doRoot : Bool) : SmtType -> SmtType
  | SmtType.TypeRef r =>
      if doSub && native_streq r sub then
        SmtType.Datatype sub
          (if doRoot then __smtx_dt_substitute root newRoot base else base)
      else
        SmtType.TypeRef r
  | SmtType.Datatype r d =>
      if doRoot && native_streq r root && decide (d = oldRoot) then
        SmtType.Datatype r newRoot
      else
        SmtType.Datatype r
          (smtx_dt_context_substitute_apply sub (__smtx_dt_lift r d base) root oldRoot newRoot
            (doSub && !native_streq r sub) (doRoot && !native_streq r root) d)
  | SmtType.DtcAppType A B =>
      SmtType.DtcAppType
        (smtx_chain_type_context_substitute_apply sub base root oldRoot newRoot
          doSub doRoot A)
        (smtx_chain_type_context_substitute_apply sub base root oldRoot newRoot
          doSub doRoot B)
  | T => T

private def smtx_dtc_context_substitute_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype)
    (doSub doRoot : Bool) : SmtDatatypeCons -> SmtDatatypeCons
  | SmtDatatypeCons.cons T c =>
      SmtDatatypeCons.cons
        (smtx_type_context_substitute_apply sub base root oldRoot newRoot doSub doRoot T)
        (smtx_dtc_context_substitute_apply sub base root oldRoot newRoot doSub doRoot c)
  | SmtDatatypeCons.unit => SmtDatatypeCons.unit

private def smtx_dt_context_substitute_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype)
    (doSub doRoot : Bool) : SmtDatatype -> SmtDatatype
  | SmtDatatype.sum c d =>
      SmtDatatype.sum
        (smtx_dtc_context_substitute_apply sub base root oldRoot newRoot doSub doRoot c)
        (smtx_dt_context_substitute_apply sub base root oldRoot newRoot doSub doRoot d)
  | SmtDatatype.null => SmtDatatype.null

private def smtx_chain_type_context_substitute_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype)
    (doSub doRoot : Bool) : SmtType -> SmtType
  | SmtType.DtcAppType A B =>
      SmtType.DtcAppType
        (smtx_chain_type_context_substitute_apply sub base root oldRoot newRoot doSub doRoot A)
        (smtx_chain_type_context_substitute_apply sub base root oldRoot newRoot doSub doRoot B)
  | T =>
      smtx_type_context_substitute_apply sub base root oldRoot newRoot doSub doRoot T

end

private theorem smtx_type_context_substitute_eq_chain_type_context_substitute_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype)
    (doSub doRoot : Bool) :
    (T : SmtType) ->
      smtx_type_context_substitute_apply sub base root oldRoot newRoot doSub doRoot T =
        smtx_chain_type_context_substitute_apply sub base root oldRoot newRoot doSub doRoot T
  | SmtType.DtcAppType A B => by
      simp [smtx_type_context_substitute_apply,
        smtx_chain_type_context_substitute_apply]
  | T => by
      cases T <;>
        simp [smtx_type_context_substitute_apply,
          smtx_chain_type_context_substitute_apply]

mutual

private theorem smtx_type_context_substitute_off_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype) :
    (T : SmtType) ->
      smtx_type_context_substitute_apply sub base root oldRoot newRoot
          false false T =
        T
  | SmtType.Datatype r d => by
      have hD :
          smtx_dt_context_substitute_apply sub (__smtx_dt_lift r d base) root oldRoot newRoot
              false false d = d :=
        smtx_dt_context_substitute_off_apply sub (__smtx_dt_lift r d base) root oldRoot newRoot d
      simp [smtx_type_context_substitute_apply, hD]
  | SmtType.DtcAppType A B => by
      have hA :
          smtx_chain_type_context_substitute_apply sub base root oldRoot newRoot
              false false A = A :=
        smtx_chain_type_context_substitute_off_apply
          sub base root oldRoot newRoot A
      have hB :
          smtx_chain_type_context_substitute_apply sub base root oldRoot newRoot
              false false B = B :=
        smtx_chain_type_context_substitute_off_apply
          sub base root oldRoot newRoot B
      simp [smtx_type_context_substitute_apply, hA, hB]
  | SmtType.None => by
      simp [smtx_type_context_substitute_apply]
  | SmtType.Bool => by
      simp [smtx_type_context_substitute_apply]
  | SmtType.Int => by
      simp [smtx_type_context_substitute_apply]
  | SmtType.Real => by
      simp [smtx_type_context_substitute_apply]
  | SmtType.RegLan => by
      simp [smtx_type_context_substitute_apply]
  | SmtType.BitVec w => by
      simp [smtx_type_context_substitute_apply]
  | SmtType.Map A B => by
      simp [smtx_type_context_substitute_apply]
  | SmtType.Set A => by
      simp [smtx_type_context_substitute_apply]
  | SmtType.Seq A => by
      simp [smtx_type_context_substitute_apply]
  | SmtType.Char => by
      simp [smtx_type_context_substitute_apply]
  | SmtType.TypeRef r => by
      simp [smtx_type_context_substitute_apply]
  | SmtType.USort i => by
      simp [smtx_type_context_substitute_apply]
  | SmtType.FunType A B => by
      simp [smtx_type_context_substitute_apply]
termination_by T => sizeOf T
decreasing_by
  all_goals simp_wf
  all_goals omega

private theorem smtx_dtc_context_substitute_off_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype) :
    (c : SmtDatatypeCons) ->
      smtx_dtc_context_substitute_apply sub base root oldRoot newRoot
          false false c =
        c
  | SmtDatatypeCons.unit => by
      simp [smtx_dtc_context_substitute_apply]
  | SmtDatatypeCons.cons T c => by
      have hT :
          smtx_type_context_substitute_apply sub base root oldRoot newRoot
              false false T = T :=
        smtx_type_context_substitute_off_apply sub base root oldRoot newRoot T
      have hC :
          smtx_dtc_context_substitute_apply sub base root oldRoot newRoot
              false false c = c :=
        smtx_dtc_context_substitute_off_apply sub base root oldRoot newRoot c
      simp [smtx_dtc_context_substitute_apply, hT, hC]
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals omega

private theorem smtx_dt_context_substitute_off_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype) :
    (d : SmtDatatype) ->
      smtx_dt_context_substitute_apply sub base root oldRoot newRoot
          false false d =
        d
  | SmtDatatype.null => by
      simp [smtx_dt_context_substitute_apply]
  | SmtDatatype.sum c d => by
      have hC :
          smtx_dtc_context_substitute_apply sub base root oldRoot newRoot
              false false c = c :=
        smtx_dtc_context_substitute_off_apply sub base root oldRoot newRoot c
      have hD :
          smtx_dt_context_substitute_apply sub base root oldRoot newRoot
              false false d = d :=
        smtx_dt_context_substitute_off_apply sub base root oldRoot newRoot d
      simp [smtx_dt_context_substitute_apply, hC, hD]
termination_by d => sizeOf d
decreasing_by
  all_goals simp_wf
  all_goals omega

private theorem smtx_chain_type_context_substitute_off_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype) :
    (T : SmtType) ->
      smtx_chain_type_context_substitute_apply sub base root oldRoot newRoot
          false false T =
        T
  | SmtType.DtcAppType A B => by
      have hA :
          smtx_chain_type_context_substitute_apply sub base root oldRoot newRoot
              false false A = A :=
        smtx_chain_type_context_substitute_off_apply
          sub base root oldRoot newRoot A
      have hB :
          smtx_chain_type_context_substitute_apply sub base root oldRoot newRoot
              false false B = B :=
        smtx_chain_type_context_substitute_off_apply
          sub base root oldRoot newRoot B
      simp [smtx_chain_type_context_substitute_apply, hA, hB]
  | SmtType.Datatype r d => by
      have hD :
          smtx_dt_context_substitute_apply sub (__smtx_dt_lift r d base) root oldRoot newRoot
              false false d = d :=
        smtx_dt_context_substitute_off_apply sub (__smtx_dt_lift r d base) root oldRoot newRoot d
      simp [smtx_chain_type_context_substitute_apply,
        smtx_type_context_substitute_apply, hD]
  | SmtType.None => by
      simp [smtx_chain_type_context_substitute_apply,
        smtx_type_context_substitute_apply]
  | SmtType.Bool => by
      simp [smtx_chain_type_context_substitute_apply,
        smtx_type_context_substitute_apply]
  | SmtType.Int => by
      simp [smtx_chain_type_context_substitute_apply,
        smtx_type_context_substitute_apply]
  | SmtType.Real => by
      simp [smtx_chain_type_context_substitute_apply,
        smtx_type_context_substitute_apply]
  | SmtType.RegLan => by
      simp [smtx_chain_type_context_substitute_apply,
        smtx_type_context_substitute_apply]
  | SmtType.BitVec w => by
      simp [smtx_chain_type_context_substitute_apply,
        smtx_type_context_substitute_apply]
  | SmtType.Map A B => by
      simp [smtx_chain_type_context_substitute_apply,
        smtx_type_context_substitute_apply]
  | SmtType.Set A => by
      simp [smtx_chain_type_context_substitute_apply,
        smtx_type_context_substitute_apply]
  | SmtType.Seq A => by
      simp [smtx_chain_type_context_substitute_apply,
        smtx_type_context_substitute_apply]
  | SmtType.Char => by
      simp [smtx_chain_type_context_substitute_apply,
        smtx_type_context_substitute_apply]
  | SmtType.TypeRef r => by
      simp [smtx_chain_type_context_substitute_apply,
        smtx_type_context_substitute_apply]
  | SmtType.USort i => by
      simp [smtx_chain_type_context_substitute_apply,
        smtx_type_context_substitute_apply]
  | SmtType.FunType A B => by
      simp [smtx_chain_type_context_substitute_apply,
        smtx_type_context_substitute_apply]
termination_by T => sizeOf T
decreasing_by
  all_goals simp_wf
  all_goals omega

end

private def smtx_value_dt_context_substitute_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype) :
    SmtValue -> SmtValue
  | SmtValue.DtCons s d i =>
      if native_streq s root && decide (d = oldRoot) then
        SmtValue.DtCons s newRoot i
      else
        SmtValue.DtCons s
          (smtx_dt_context_substitute_apply sub base root oldRoot newRoot
            (!native_streq s sub) (!native_streq s root) d) i
  | SmtValue.Apply f a =>
      SmtValue.Apply
        (smtx_value_dt_context_substitute_apply sub base root oldRoot newRoot f)
        (smtx_value_dt_context_substitute_apply sub base root oldRoot newRoot a)
  | v => v

private def smtx_dt_context_substitute_value_body_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype)
    (s : native_String) (d : SmtDatatype) : SmtDatatype :=
  if native_streq s root && decide (d = oldRoot) then
    newRoot
  else
    smtx_dt_context_substitute_apply sub base root oldRoot newRoot
      (!native_streq s sub) (!native_streq s root) d

private theorem smtx_value_dt_context_substitute_apply_num_args
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype) :
    (v : SmtValue) ->
      vsm_num_apply_args
          (smtx_value_dt_context_substitute_apply sub base root oldRoot newRoot v) =
        vsm_num_apply_args v
  | SmtValue.Apply f a => by
      simp [smtx_value_dt_context_substitute_apply, vsm_num_apply_args,
        smtx_value_dt_context_substitute_apply_num_args sub base root oldRoot newRoot f]
  | SmtValue.NotValue => rfl
  | SmtValue.Boolean _ => rfl
  | SmtValue.Numeral _ => rfl
  | SmtValue.Rational _ => rfl
  | SmtValue.Binary _ _ => rfl
  | SmtValue.Map _ => rfl
  | SmtValue.Fun _ _ _ => rfl
  | SmtValue.Set _ => rfl
  | SmtValue.Seq _ => rfl
  | SmtValue.Char _ => rfl
  | SmtValue.UValue _ _ => rfl
  | SmtValue.RegLan _ => rfl
  | SmtValue.DtCons sh dh ih => by
      by_cases h :
          native_streq sh root = true ∧ dh = oldRoot <;>
        simp [smtx_value_dt_context_substitute_apply, h, vsm_num_apply_args]

private theorem smtx_value_dt_context_substitute_apply_head
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype) :
    (v : SmtValue) -> {s : native_String} -> {d : SmtDatatype} ->
      {i : native_Nat} ->
      __smtx_apply_head_value v = SmtValue.DtCons s d i ->
      __smtx_apply_head_value
          (smtx_value_dt_context_substitute_apply
            sub base root oldRoot newRoot v) =
        SmtValue.DtCons s
          (smtx_dt_context_substitute_value_body_apply
            sub base root oldRoot newRoot s d) i
  | SmtValue.Apply f a, s, d, i, hHead => by
      simpa [smtx_value_dt_context_substitute_apply, __smtx_apply_head_value] using
        smtx_value_dt_context_substitute_apply_head
          sub base root oldRoot newRoot f hHead
  | SmtValue.DtCons sh dh ih, s, d, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
      rcases hHead with ⟨rfl, hEq⟩
      rcases hEq with ⟨rfl, rfl⟩
      by_cases h :
          native_streq sh root = true ∧ dh = oldRoot <;>
        simp [smtx_value_dt_context_substitute_apply,
          smtx_dt_context_substitute_value_body_apply, h, __smtx_apply_head_value]
  | SmtValue.NotValue, s, d, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Boolean b, s, d, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Numeral n, s, d, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Rational q, s, d, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Binary w n, s, d, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Map m, s, d, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Fun _ _ _, s, d, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Set m, s, d, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Seq ss, s, d, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Char c, s, d, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.UValue k e, s, d, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.RegLan r, s, d, i, hHead => by
      simp [__smtx_apply_head_value] at hHead

private theorem smtx_value_dt_context_substitute_apply_head_of_root
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype) :
    (v : SmtValue) -> {i : native_Nat} ->
      __smtx_apply_head_value v = SmtValue.DtCons root oldRoot i ->
      __smtx_apply_head_value
          (smtx_value_dt_context_substitute_apply sub base root oldRoot newRoot v) =
        SmtValue.DtCons root newRoot i
  | SmtValue.DtCons s d i', i, hHead => by
      simp [__smtx_apply_head_value] at hHead
      rcases hHead with ⟨rfl, hRest⟩
      rcases hRest with ⟨rfl, rfl⟩
      simp [smtx_value_dt_context_substitute_apply, __smtx_apply_head_value,
        native_streq]
  | SmtValue.Apply f a, i, hHead => by
      have hHeadF : __smtx_apply_head_value f = SmtValue.DtCons root oldRoot i := by
        simpa [__smtx_apply_head_value] using hHead
      have hRec :=
        smtx_value_dt_context_substitute_apply_head_of_root
          sub base root oldRoot newRoot f hHeadF
      simpa [smtx_value_dt_context_substitute_apply, __smtx_apply_head_value] using hRec
  | SmtValue.NotValue, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Boolean _, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Numeral _, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Rational _, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Binary _ _, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Map _, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Fun _ _ _, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Set _, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Seq _, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Char _, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.UValue _ _, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.RegLan _, i, hHead => by
      simp [__smtx_apply_head_value] at hHead

private theorem smtx_value_dt_context_substitute_apply_arg_nth
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype) :
    (v : SmtValue) -> (j : native_Nat) ->
      __smtx_apply_arg_nth_value
          (smtx_value_dt_context_substitute_apply sub base root oldRoot newRoot v) j
          (vsm_num_apply_args
            (smtx_value_dt_context_substitute_apply sub base root oldRoot newRoot v)) =
        smtx_value_dt_context_substitute_apply sub base root oldRoot newRoot
          (__smtx_apply_arg_nth_value v j (vsm_num_apply_args v))
  | SmtValue.Apply f a, j => by
      by_cases hEq : native_nateq j (vsm_num_apply_args f) = true
      · simp [smtx_value_dt_context_substitute_apply, __smtx_apply_arg_nth_value,
          vsm_num_apply_args,
          smtx_value_dt_context_substitute_apply_num_args sub base root oldRoot newRoot f,
          native_ite, hEq]
      · have hArg :=
          smtx_value_dt_context_substitute_apply_arg_nth
            sub base root oldRoot newRoot f j
        simp [smtx_value_dt_context_substitute_apply, __smtx_apply_arg_nth_value,
          vsm_num_apply_args,
          smtx_value_dt_context_substitute_apply_num_args sub base root oldRoot newRoot f,
          native_ite, hEq]
        simpa [smtx_value_dt_context_substitute_apply_num_args
          sub base root oldRoot newRoot f] using hArg
  | SmtValue.NotValue, _ => rfl
  | SmtValue.Boolean _, _ => rfl
  | SmtValue.Numeral _, _ => rfl
  | SmtValue.Rational _, _ => rfl
  | SmtValue.Binary _ _, _ => rfl
  | SmtValue.Map _, _ => rfl
  | SmtValue.Fun _ _ _, _ => rfl
  | SmtValue.Set _, _ => rfl
  | SmtValue.Seq _, _ => rfl
  | SmtValue.Char _, _ => rfl
  | SmtValue.UValue _ _, _ => rfl
  | SmtValue.RegLan _, _ => rfl
  | SmtValue.DtCons sh dh ih, _ => by
      by_cases h :
          native_streq sh root = true ∧ dh = oldRoot <;>
        simp [smtx_value_dt_context_substitute_apply, h, __smtx_apply_arg_nth_value]

private theorem smtx_dtc_context_substitute_num_sels_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype)
    (doSub doRoot : Bool) :
    (c : SmtDatatypeCons) ->
      __smtx_dtc_num_sels
          (smtx_dtc_context_substitute_apply sub base root oldRoot newRoot doSub doRoot c) =
        __smtx_dtc_num_sels c
  | SmtDatatypeCons.unit => by
      simp [smtx_dtc_context_substitute_apply, __smtx_dtc_num_sels]
  | SmtDatatypeCons.cons T c => by
      simp [smtx_dtc_context_substitute_apply, __smtx_dtc_num_sels,
        smtx_dtc_context_substitute_num_sels_apply sub base root oldRoot newRoot
          doSub doRoot c]

private theorem smtx_dt_context_substitute_num_sels_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype)
    (doSub doRoot : Bool) :
    (d : SmtDatatype) -> (i : native_Nat) ->
      __smtx_dt_num_sels
          (smtx_dt_context_substitute_apply sub base root oldRoot newRoot doSub doRoot d) i =
        __smtx_dt_num_sels d i
  | SmtDatatype.null, i => by
      cases i <;>
        simp [smtx_dt_context_substitute_apply, __smtx_dt_num_sels]
  | SmtDatatype.sum c d, native_nat_zero => by
      simp [smtx_dt_context_substitute_apply, __smtx_dt_num_sels,
        smtx_dtc_context_substitute_num_sels_apply]
  | SmtDatatype.sum c d, native_nat_succ i => by
      simp [smtx_dt_context_substitute_apply, __smtx_dt_num_sels,
        smtx_dt_context_substitute_num_sels_apply sub base root oldRoot newRoot
          doSub doRoot d i]

private theorem smtx_ret_typeof_sel_rec_context_substitute_cons_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype)
    (doSub doRoot : Bool) :
    (c : SmtDatatypeCons) -> (d : SmtDatatype) -> (j : native_Nat) ->
      __smtx_ret_typeof_sel_rec
          (SmtDatatype.sum
            (smtx_dtc_context_substitute_apply sub base root oldRoot newRoot
              doSub doRoot c)
            (smtx_dt_context_substitute_apply sub base root oldRoot newRoot
              doSub doRoot d))
          native_nat_zero j =
        smtx_type_context_substitute_apply sub base root oldRoot newRoot doSub doRoot
          (__smtx_ret_typeof_sel_rec (SmtDatatype.sum c d) native_nat_zero j)
  | SmtDatatypeCons.unit, d, j => by
      cases j <;>
        simp [smtx_dtc_context_substitute_apply, __smtx_ret_typeof_sel_rec,
          smtx_type_context_substitute_apply]
  | SmtDatatypeCons.cons T c, d, native_nat_zero => by
      cases T <;>
        simp [smtx_dtc_context_substitute_apply, __smtx_ret_typeof_sel_rec,
          smtx_type_context_substitute_apply]
  | SmtDatatypeCons.cons T c, d, native_nat_succ j => by
      cases T <;>
        simp [smtx_dtc_context_substitute_apply, __smtx_ret_typeof_sel_rec,
          smtx_ret_typeof_sel_rec_context_substitute_cons_apply
            sub base root oldRoot newRoot doSub doRoot c d j]

private theorem smtx_ret_typeof_sel_rec_context_substitute_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype)
    (doSub doRoot : Bool) :
    (d : SmtDatatype) -> (i j : native_Nat) ->
      __smtx_ret_typeof_sel_rec
          (smtx_dt_context_substitute_apply sub base root oldRoot newRoot
            doSub doRoot d) i j =
        smtx_type_context_substitute_apply sub base root oldRoot newRoot doSub doRoot
          (__smtx_ret_typeof_sel_rec d i j)
  | SmtDatatype.null, i, j => by
      cases i <;> cases j <;>
        simp [smtx_dt_context_substitute_apply, __smtx_ret_typeof_sel_rec,
          smtx_type_context_substitute_apply]
  | SmtDatatype.sum c d, native_nat_zero, j => by
      simpa [smtx_dt_context_substitute_apply] using
        smtx_ret_typeof_sel_rec_context_substitute_cons_apply
          sub base root oldRoot newRoot doSub doRoot c d j
  | SmtDatatype.sum c d, native_nat_succ i, j => by
      simpa [smtx_dt_context_substitute_apply, __smtx_ret_typeof_sel_rec] using
        smtx_ret_typeof_sel_rec_context_substitute_apply
          sub base root oldRoot newRoot doSub doRoot d i j

private theorem smtx_typeof_dt_cons_value_rec_context_substitute_cons_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype)
    (doSub doRoot : Bool)
    (T : SmtType) :
    (c : SmtDatatypeCons) -> (d : SmtDatatype) ->
      __smtx_typeof_dt_cons_value_rec
          (smtx_chain_type_context_substitute_apply sub base root oldRoot newRoot doSub doRoot T)
          (SmtDatatype.sum
            (smtx_dtc_context_substitute_apply sub base root oldRoot newRoot
              doSub doRoot c)
            (smtx_dt_context_substitute_apply sub base root oldRoot newRoot
              doSub doRoot d))
          native_nat_zero =
        smtx_chain_type_context_substitute_apply
          sub base root oldRoot newRoot doSub doRoot
          (__smtx_typeof_dt_cons_value_rec T (SmtDatatype.sum c d) native_nat_zero)
  | SmtDatatypeCons.unit, d => by
      simp [smtx_dtc_context_substitute_apply, __smtx_typeof_dt_cons_value_rec]
  | SmtDatatypeCons.cons U c, d => by
      simp [smtx_dtc_context_substitute_apply, __smtx_typeof_dt_cons_value_rec,
        smtx_chain_type_context_substitute_apply,
        smtx_type_context_substitute_eq_chain_type_context_substitute_apply,
        smtx_typeof_dt_cons_value_rec_context_substitute_cons_apply
          sub base root oldRoot newRoot doSub doRoot T c d]

private theorem smtx_typeof_dt_cons_value_rec_context_substitute_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype)
    (doSub doRoot : Bool)
    (T : SmtType) :
    (d : SmtDatatype) -> (i : native_Nat) ->
      __smtx_typeof_dt_cons_value_rec
          (smtx_chain_type_context_substitute_apply sub base root oldRoot newRoot doSub doRoot T)
          (smtx_dt_context_substitute_apply sub base root oldRoot newRoot doSub doRoot d)
          i =
        smtx_chain_type_context_substitute_apply
          sub base root oldRoot newRoot doSub doRoot
          (__smtx_typeof_dt_cons_value_rec T d i)
  | SmtDatatype.null, i => by
      cases i <;>
        simp [smtx_dt_context_substitute_apply, __smtx_typeof_dt_cons_value_rec,
          smtx_chain_type_context_substitute_apply, smtx_type_context_substitute_apply]
  | SmtDatatype.sum c d, native_nat_zero => by
      simpa [smtx_dt_context_substitute_apply] using
        smtx_typeof_dt_cons_value_rec_context_substitute_cons_apply
          sub base root oldRoot newRoot doSub doRoot T c d
  | SmtDatatype.sum c d, native_nat_succ i => by
      simpa [smtx_dt_context_substitute_apply, __smtx_typeof_dt_cons_value_rec] using
        smtx_typeof_dt_cons_value_rec_context_substitute_apply
          sub base root oldRoot newRoot doSub doRoot T d i

private theorem dt_cons_applied_type_rec_context_substitute_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype)
    (doSub doRoot : Bool)
    (s : native_String) (d0 d0' : SmtDatatype)
    (hBaseCtx :
      smtx_chain_type_context_substitute_apply
          sub base root oldRoot newRoot doSub doRoot
          (SmtType.Datatype s d0) =
        SmtType.Datatype s d0') :
    (d : SmtDatatype) -> (i n : native_Nat) ->
      dt_cons_applied_type_rec s d0'
          (smtx_dt_context_substitute_apply
            sub base root oldRoot newRoot doSub doRoot d) i n =
        smtx_chain_type_context_substitute_apply
          sub base root oldRoot newRoot doSub doRoot
          (dt_cons_applied_type_rec s d0 d i n)
  | d, i, native_nat_zero => by
      simpa [dt_cons_applied_type_rec, hBaseCtx] using
        smtx_typeof_dt_cons_value_rec_context_substitute_apply
          sub base root oldRoot newRoot doSub doRoot
          (SmtType.Datatype s d0) d i
  | SmtDatatype.null, i, native_nat_succ n => by
      cases i <;>
        simp [smtx_dt_context_substitute_apply, dt_cons_applied_type_rec,
          smtx_chain_type_context_substitute_apply,
          smtx_type_context_substitute_apply]
  | SmtDatatype.sum SmtDatatypeCons.unit d, native_nat_zero,
      native_nat_succ n => by
      cases n <;>
        simp [smtx_dt_context_substitute_apply, smtx_dtc_context_substitute_apply,
          dt_cons_applied_type_rec, smtx_chain_type_context_substitute_apply,
          smtx_type_context_substitute_apply]
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, native_nat_zero,
      native_nat_succ n => by
      simpa [smtx_dt_context_substitute_apply, smtx_dtc_context_substitute_apply,
        dt_cons_applied_type_rec] using
        dt_cons_applied_type_rec_context_substitute_apply
          sub base root oldRoot newRoot doSub doRoot s d0 d0' hBaseCtx
          (SmtDatatype.sum c d) native_nat_zero n
  | SmtDatatype.sum c d, native_nat_succ i, native_nat_succ n => by
      simpa [smtx_dt_context_substitute_apply, dt_cons_applied_type_rec] using
        dt_cons_applied_type_rec_context_substitute_apply
          sub base root oldRoot newRoot doSub doRoot s d0 d0' hBaseCtx
          d i (native_nat_succ n)

private def smtx_type_chain_field_wf_rec (refs : RefList) : SmtType -> Prop
  | SmtType.DtcAppType A B =>
      smtx_type_field_wf_rec A refs ∧ smtx_type_chain_field_wf_rec refs B
  | T => smtx_type_field_wf_rec T refs

private theorem smtx_type_field_wf_rec_ne_none
    {T : SmtType} {refs : RefList}
    (h : smtx_type_field_wf_rec T refs) :
    T ≠ SmtType.None := by
  cases T <;> simp [smtx_type_field_wf_rec, __smtx_type_wf_rec] at h ⊢

private theorem smtx_type_chain_field_wf_rec_of_field_wf
    {T : SmtType} {refs : RefList}
    (h : smtx_type_field_wf_rec T refs) :
    smtx_type_chain_field_wf_rec refs T := by
  cases T <;> simp [smtx_type_chain_field_wf_rec,
    smtx_type_field_wf_rec, __smtx_type_wf_rec] at h ⊢
  all_goals exact h

private theorem smtx_type_chain_field_wf_rec_head_of_dtc_app
    {A B : SmtType} {refs : RefList}
    (h : smtx_type_chain_field_wf_rec refs (SmtType.DtcAppType A B)) :
    smtx_type_field_wf_rec A refs := by
  simpa [smtx_type_chain_field_wf_rec] using h.1

private theorem smtx_type_chain_field_wf_rec_tail_of_dtc_app
    {A B : SmtType} {refs : RefList}
    (h : smtx_type_chain_field_wf_rec refs (SmtType.DtcAppType A B)) :
    smtx_type_chain_field_wf_rec refs B := by
  simpa [smtx_type_chain_field_wf_rec] using h.2

/--
EO-to-SMT type translation is injective on datatype-constructor result chains
whose fields are well formed.
-/
private theorem eo_to_smt_type_injective_of_chain_field_wf_rec
    {T U : Term} {A : SmtType} {refs : RefList}
    (hT : __eo_to_smt_type T = A)
    (hU : __eo_to_smt_type U = A)
    (hWF : smtx_type_chain_field_wf_rec refs A) :
    T = U := by
  cases A with
  | DtcAppType A B =>
      rcases eo_to_smt_type_eq_dtc_app hT with ⟨T1, T2, rfl, hT1, hT2⟩
      rcases eo_to_smt_type_eq_dtc_app hU with ⟨U1, U2, rfl, hU1, hU2⟩
      have hA : smtx_type_field_wf_rec A refs :=
        smtx_type_chain_field_wf_rec_head_of_dtc_app hWF
      have hB : smtx_type_chain_field_wf_rec refs B :=
        smtx_type_chain_field_wf_rec_tail_of_dtc_app hWF
      have h1 : T1 = U1 :=
        eo_to_smt_type_injective_of_field_wf_rec hT1 hU1 hA
      have h2 : T2 = U2 :=
        eo_to_smt_type_injective_of_chain_field_wf_rec hT2 hU2 hB
      subst U1
      subst U2
      rfl
  | None =>
      exact eo_to_smt_type_injective_of_field_wf_rec hT hU
        (by simpa [smtx_type_chain_field_wf_rec] using hWF)
  | Bool =>
      exact eo_to_smt_type_injective_of_field_wf_rec hT hU
        (by simpa [smtx_type_chain_field_wf_rec] using hWF)
  | Int =>
      exact eo_to_smt_type_injective_of_field_wf_rec hT hU
        (by simpa [smtx_type_chain_field_wf_rec] using hWF)
  | Real =>
      exact eo_to_smt_type_injective_of_field_wf_rec hT hU
        (by simpa [smtx_type_chain_field_wf_rec] using hWF)
  | RegLan =>
      exact eo_to_smt_type_injective_of_field_wf_rec hT hU
        (by simpa [smtx_type_chain_field_wf_rec] using hWF)
  | BitVec w =>
      exact eo_to_smt_type_injective_of_field_wf_rec hT hU
        (by simpa [smtx_type_chain_field_wf_rec] using hWF)
  | Map A B =>
      exact eo_to_smt_type_injective_of_field_wf_rec hT hU
        (by simpa [smtx_type_chain_field_wf_rec] using hWF)
  | Set A =>
      exact eo_to_smt_type_injective_of_field_wf_rec hT hU
        (by simpa [smtx_type_chain_field_wf_rec] using hWF)
  | Seq A =>
      exact eo_to_smt_type_injective_of_field_wf_rec hT hU
        (by simpa [smtx_type_chain_field_wf_rec] using hWF)
  | Char =>
      exact eo_to_smt_type_injective_of_field_wf_rec hT hU
        (by simpa [smtx_type_chain_field_wf_rec] using hWF)
  | Datatype s d =>
      exact eo_to_smt_type_injective_of_field_wf_rec hT hU
        (by simpa [smtx_type_chain_field_wf_rec] using hWF)
  | TypeRef s =>
      exact eo_to_smt_type_injective_of_field_wf_rec hT hU
        (by simpa [smtx_type_chain_field_wf_rec] using hWF)
  | USort i =>
      exact eo_to_smt_type_injective_of_field_wf_rec hT hU
        (by simpa [smtx_type_chain_field_wf_rec] using hWF)
  | FunType A B =>
      exact eo_to_smt_type_injective_of_field_wf_rec hT hU
        (by simpa [smtx_type_chain_field_wf_rec] using hWF)
termination_by A

private theorem dt_cons_applied_type_rec_substitute_ne_none_apply
    (sub : native_String) (base : SmtDatatype)
    (s : native_String) (dBase dBase' : SmtDatatype) :
    (d : SmtDatatype) -> (i n : native_Nat) ->
      dt_cons_applied_type_rec s dBase d i n ≠ SmtType.None ->
      dt_cons_applied_type_rec s dBase'
          (__smtx_dt_substitute sub base d) i n ≠ SmtType.None
  | SmtDatatype.null, i, n, hNN => by
      exfalso
      apply hNN
      cases i <;> cases n <;>
        simp [dt_cons_applied_type_rec, __smtx_typeof_dt_cons_value_rec]
  | SmtDatatype.sum SmtDatatypeCons.unit d, native_nat_zero, native_nat_zero, hNN => by
      simp [dt_cons_applied_type_rec, __smtx_dt_substitute,
        __smtx_dtc_substitute, __smtx_typeof_dt_cons_value_rec]
  | SmtDatatype.sum SmtDatatypeCons.unit d, native_nat_zero, native_nat_succ n, hNN => by
      simp [dt_cons_applied_type_rec] at hNN
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, native_nat_zero,
      native_nat_zero, hNN => by
      cases U <;>
        simp [dt_cons_applied_type_rec, __smtx_dt_substitute,
          __smtx_dtc_substitute, __smtx_typeof_dt_cons_value_rec]
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, native_nat_zero,
      native_nat_succ n, hNN => by
      have hTailNN :
          dt_cons_applied_type_rec s dBase (SmtDatatype.sum c d)
              native_nat_zero n ≠
            SmtType.None := by
        simpa [dt_cons_applied_type_rec] using hNN
      have hRec :=
        dt_cons_applied_type_rec_substitute_ne_none_apply
          sub base s dBase dBase' (SmtDatatype.sum c d)
          native_nat_zero n hTailNN
      cases U <;>
        simpa [dt_cons_applied_type_rec, __smtx_dt_substitute,
          __smtx_dtc_substitute] using hRec
  | SmtDatatype.sum c SmtDatatype.null, native_nat_succ i, n, hNN => by
      exfalso
      apply hNN
      cases n <;>
        simp [dt_cons_applied_type_rec, __smtx_typeof_dt_cons_value_rec]
  | SmtDatatype.sum c (SmtDatatype.sum cTail dTail), native_nat_succ i, n, hNN => by
      have hTailNN :
          dt_cons_applied_type_rec s dBase
              (SmtDatatype.sum cTail dTail) i n ≠
            SmtType.None := by
        cases n <;>
          simpa [dt_cons_applied_type_rec, __smtx_typeof_dt_cons_value_rec] using hNN
      have hRec :=
        dt_cons_applied_type_rec_substitute_ne_none_apply
          sub base s dBase dBase' (SmtDatatype.sum cTail dTail) i n hTailNN
      cases n <;>
        simpa [dt_cons_applied_type_rec, __smtx_dt_substitute,
          __smtx_typeof_dt_cons_value_rec] using hRec

private theorem dt_cons_applied_type_rec_substitute_reflect_ne_none_apply
    (sub : native_String) (base : SmtDatatype)
    (s : native_String) (dBase dBase' : SmtDatatype) :
    (d : SmtDatatype) -> (i n : native_Nat) ->
      dt_cons_applied_type_rec s dBase'
          (__smtx_dt_substitute sub base d) i n ≠ SmtType.None ->
      dt_cons_applied_type_rec s dBase d i n ≠ SmtType.None
  | SmtDatatype.null, i, n, hNN => by
      exfalso
      apply hNN
      cases i <;> cases n <;>
        simp [dt_cons_applied_type_rec, __smtx_dt_substitute,
          __smtx_typeof_dt_cons_value_rec]
  | SmtDatatype.sum SmtDatatypeCons.unit d, native_nat_zero, native_nat_zero, hNN => by
      simp [dt_cons_applied_type_rec, __smtx_typeof_dt_cons_value_rec]
  | SmtDatatype.sum SmtDatatypeCons.unit d, native_nat_zero, native_nat_succ n, hNN => by
      exfalso
      apply hNN
      simp [dt_cons_applied_type_rec, __smtx_dt_substitute,
        __smtx_dtc_substitute]
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, native_nat_zero,
      native_nat_zero, hNN => by
      simp [dt_cons_applied_type_rec, __smtx_typeof_dt_cons_value_rec]
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, native_nat_zero,
      native_nat_succ n, hNN => by
      have hTailNN :
          dt_cons_applied_type_rec s dBase'
              (__smtx_dt_substitute sub base (SmtDatatype.sum c d))
              native_nat_zero n ≠
            SmtType.None := by
        cases U <;>
          simpa [dt_cons_applied_type_rec, __smtx_dt_substitute,
            __smtx_dtc_substitute] using hNN
      have hRec :=
        dt_cons_applied_type_rec_substitute_reflect_ne_none_apply
          sub base s dBase dBase' (SmtDatatype.sum c d)
          native_nat_zero n hTailNN
      simpa [dt_cons_applied_type_rec] using hRec
  | SmtDatatype.sum c SmtDatatype.null, native_nat_succ i, n, hNN => by
      exfalso
      apply hNN
      cases n <;>
        simp [dt_cons_applied_type_rec, __smtx_dt_substitute,
          __smtx_typeof_dt_cons_value_rec]
  | SmtDatatype.sum c (SmtDatatype.sum cTail dTail), native_nat_succ i, n, hNN => by
      have hTailNN :
          dt_cons_applied_type_rec s dBase'
              (__smtx_dt_substitute sub base (SmtDatatype.sum cTail dTail))
              i n ≠
            SmtType.None := by
        cases n <;>
          simpa [dt_cons_applied_type_rec, __smtx_dt_substitute,
            __smtx_typeof_dt_cons_value_rec] using hNN
      have hRec :=
        dt_cons_applied_type_rec_substitute_reflect_ne_none_apply
          sub base s dBase dBase' (SmtDatatype.sum cTail dTail) i n hTailNN
      cases n <;>
        simpa [dt_cons_applied_type_rec, __smtx_typeof_dt_cons_value_rec] using hRec

/-- Extract a non-`TypeRef` field's (full/unfold) well-formedness from an enclosing cons
well-formedness. The `TypeRef`-field case is handled by the `dt_cons_wf_rec` first clause and is
excluded here via `hNotRef`. -/
private theorem smtx_type_field_wf_of_full_cons_wf
    {TF T : SmtType} {cF cU : SmtDatatypeCons}
    (hNotRef : ∀ s, T ≠ SmtType.TypeRef s)
    (h : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons TF cF) (SmtDatatypeCons.cons T cU) = true) :
    __smtx_type_wf_rec TF T = true := by
  have hgen : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons TF cF) (SmtDatatypeCons.cons T cU) =
      native_ite (native_and (native_inhabited_type TF) (__smtx_type_wf_rec TF T))
        (__smtx_dt_cons_wf_rec cF cU) false := by
    cases T with
    | TypeRef s => exact absurd rfl (hNotRef s)
    | _ => simp [__smtx_dt_cons_wf_rec]
  rw [hgen] at h
  cases hb : native_and (native_inhabited_type TF) (__smtx_type_wf_rec TF T) with
  | false => rw [hb] at h; exact absurd h (by simp [native_ite])
  | true => simp only [native_and, Bool.and_eq_true] at hb; exact hb.2

mutual

private theorem smtx_type_context_substitute_no_root_of_field_wf_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype) :
    (T : SmtType) -> {refs : RefList} ->
      smtx_type_field_wf_rec T refs ->
      smtx_type_context_substitute_apply sub base root oldRoot newRoot
          true false T =
        smtx_type_substitute_top_apply sub base T
  | SmtType.TypeRef r, refs, _hWf => by
      by_cases hEq : r = sub
      · simp [smtx_type_context_substitute_apply,
          smtx_type_substitute_top_apply, native_ite, native_streq, hEq]
      · have hNe : sub ≠ r := by
          intro hs
          exact hEq hs.symm
        simp [smtx_type_context_substitute_apply,
          smtx_type_substitute_top_apply, native_ite, native_streq, hEq, hNe]
  | SmtType.Datatype r d, refs, hWf => by
      by_cases hEq : r = sub
      · subst r
        have hOff :
            smtx_dt_context_substitute_apply sub (__smtx_dt_lift sub d base) root oldRoot newRoot
                false false d = d :=
          smtx_dt_context_substitute_off_apply
            sub (__smtx_dt_lift sub d base) root oldRoot newRoot d
        simp [smtx_type_context_substitute_apply,
          smtx_type_substitute_top_apply, native_ite, native_streq, hOff]
      · have hDt :
            smtx_dt_context_substitute_apply sub (__smtx_dt_lift r d base) root oldRoot newRoot
                true false d =
              __smtx_dt_substitute sub (__smtx_dt_lift r d base) d := by
            exact smtx_dt_context_substitute_no_root_of_wf_apply
              sub (__smtx_dt_lift r d base) root oldRoot newRoot d
              (refs := native_reflist_nil)
              (smtx_dt_wf_rec_of_datatype_type_wf_rec_apply (by
                simpa [smtx_type_field_wf_rec] using hWf))
              (alignDt_subst r d d)
        have hNe : sub ≠ r := by
          intro hs
          exact hEq hs.symm
        simp [smtx_type_context_substitute_apply,
          smtx_type_substitute_top_apply, native_ite, native_streq, hEq,
          hNe, hDt]
  | SmtType.DtcAppType A B, refs, hWf => by
      simp [smtx_type_field_wf_rec, __smtx_type_wf_rec] at hWf
  | SmtType.None, refs, hWf => by
      simp [smtx_type_field_wf_rec, __smtx_type_wf_rec] at hWf
  | SmtType.Bool, refs, hWf => by
      simp [smtx_type_context_substitute_apply, smtx_type_substitute_top_apply
        ]
  | SmtType.Int, refs, hWf => by
      simp [smtx_type_context_substitute_apply, smtx_type_substitute_top_apply
        ]
  | SmtType.Real, refs, hWf => by
      simp [smtx_type_context_substitute_apply, smtx_type_substitute_top_apply
        ]
  | SmtType.RegLan, refs, hWf => by
      simp [smtx_type_field_wf_rec, __smtx_type_wf_rec] at hWf
  | SmtType.BitVec w, refs, hWf => by
      simp [smtx_type_context_substitute_apply, smtx_type_substitute_top_apply
        ]
  | SmtType.Map A B, refs, hWf => by
      simp [smtx_type_context_substitute_apply, smtx_type_substitute_top_apply
        ]
  | SmtType.Set A, refs, hWf => by
      simp [smtx_type_context_substitute_apply, smtx_type_substitute_top_apply
        ]
  | SmtType.Seq A, refs, hWf => by
      simp [smtx_type_context_substitute_apply, smtx_type_substitute_top_apply
        ]
  | SmtType.Char, refs, hWf => by
      simp [smtx_type_context_substitute_apply, smtx_type_substitute_top_apply
        ]
  | SmtType.USort i, refs, hWf => by
      simp [smtx_type_context_substitute_apply, smtx_type_substitute_top_apply
        ]
  | SmtType.FunType A B, refs, hWf => by
      simp [smtx_type_context_substitute_apply, smtx_type_substitute_top_apply
        ]

-- TODO(typeWf-0701 aliasing refactor): same reflist-scoped gap as the chain-selector cluster
-- above; signatures corrected to a full/unfold `SmtDatatypeCons`/`SmtDatatype` pair, bodies
-- previously left unfinished. Both `private`, no external callers.
private theorem smtx_dtc_context_substitute_no_root_of_wf_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype) :
    (c : SmtDatatypeCons) -> {refs : RefList} -> {cF : SmtDatatypeCons} ->
      __smtx_dt_cons_wf_rec cF c = true ->
      alignDtc cF c = true ->
      smtx_dtc_context_substitute_apply sub base root oldRoot newRoot
          true false c =
        __smtx_dtc_substitute sub base c
  | SmtDatatypeCons.unit, refs, cF, hWf, hAlign => by
      simp [smtx_dtc_context_substitute_apply, __smtx_dtc_substitute]
  | SmtDatatypeCons.cons T ctail, refs, cF, hWf, hAlign => by
      cases cF with
      | unit => simp [__smtx_dt_cons_wf_rec] at hWf
      | cons TF cFtail =>
          have hTail : __smtx_dt_cons_wf_rec cFtail ctail = true :=
            smtx_dt_cons_wf_rec_tail_of_true hWf
          simp only [alignDtc, native_and, Bool.and_eq_true] at hAlign
          obtain ⟨hAlignHead, hAlignTail⟩ := hAlign
          have hTailEq :
              smtx_dtc_context_substitute_apply sub base root oldRoot newRoot true false ctail =
                __smtx_dtc_substitute sub base ctail :=
            smtx_dtc_context_substitute_no_root_of_wf_apply sub base root oldRoot newRoot ctail
              (refs := native_reflist_nil) (cF := cFtail) hTail hAlignTail
          simp only [smtx_dtc_context_substitute_apply, __smtx_dtc_substitute]
          rw [hTailEq]
          congr 1
          cases T
          case TypeRef sU =>
              by_cases hEq : sU = sub
              · subst sU
                simp [smtx_type_context_substitute_apply, __smtx_type_substitute,
                  native_ite, native_streq]
              · have hNe : sub ≠ sU := fun h => hEq h.symm
                simp [smtx_type_context_substitute_apply, __smtx_type_substitute,
                  native_ite, native_streq, hEq, hNe]
          case Datatype r d' =>
              cases TF
              case Datatype rF dF =>
                  have hFieldWf :
                      __smtx_type_wf_rec (SmtType.Datatype rF dF) (SmtType.Datatype r d') = true :=
                    smtx_type_field_wf_of_full_cons_wf (by intro s h; simp at h) hWf
                  have hDtWf :
                      __smtx_dt_wf_rec (__smtx_dt_substitute rF dF dF) d' = true := by
                    simpa [__smtx_type_wf_rec] using hFieldWf
                  simp only [alignTy] at hAlignHead
                  have hAlignD : alignDt (__smtx_dt_substitute rF dF dF) d' = true :=
                    alignDt_trans _ _ _ (alignDt_subst rF dF dF) hAlignHead
                  by_cases hEq : r = sub
                  · subst r
                    have hOff :
                        smtx_dt_context_substitute_apply sub (__smtx_dt_lift sub d' base)
                            root oldRoot newRoot false false d' = d' :=
                      smtx_dt_context_substitute_off_apply sub (__smtx_dt_lift sub d' base)
                        root oldRoot newRoot d'
                    simp [smtx_type_context_substitute_apply, __smtx_type_substitute,
                      native_ite, native_streq, hOff]
                  · have hNe : sub ≠ r := fun h => hEq h.symm
                    have hRec :
                        smtx_dt_context_substitute_apply sub (__smtx_dt_lift r d' base)
                            root oldRoot newRoot true false d' =
                          __smtx_dt_substitute sub (__smtx_dt_lift r d' base) d' :=
                      smtx_dt_context_substitute_no_root_of_wf_apply sub (__smtx_dt_lift r d' base)
                        root oldRoot newRoot d' (refs := native_reflist_nil)
                        (dF := __smtx_dt_substitute rF dF dF) hDtWf hAlignD
                    simp [smtx_type_context_substitute_apply, __smtx_type_substitute,
                      native_ite, native_streq, hEq, hNe, hRec]
              all_goals simp [alignTy] at hAlignHead
          case DtcAppType A B =>
              exfalso
              have hFieldWf :
                  __smtx_type_wf_rec TF (SmtType.DtcAppType A B) = true :=
                smtx_type_field_wf_of_full_cons_wf (by intro s h; simp at h) hWf
              simp [__smtx_type_wf_rec] at hFieldWf
          all_goals
            simp [smtx_type_context_substitute_apply, __smtx_type_substitute]

private theorem smtx_dt_context_substitute_no_root_of_wf_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype) :
    (d : SmtDatatype) -> {refs : RefList} -> {dF : SmtDatatype} ->
      __smtx_dt_wf_rec dF d = true ->
      alignDt dF d = true ->
      smtx_dt_context_substitute_apply sub base root oldRoot newRoot
          true false d =
        __smtx_dt_substitute sub base d
  | SmtDatatype.null, refs, dF, hWf, hAlign => by
      simp [smtx_dt_context_substitute_apply, __smtx_dt_substitute]
  | SmtDatatype.sum c d2, refs, dF, hWf, hAlign => by
      cases dF with
      | null => simp [__smtx_dt_wf_rec] at hWf
      | sum cF dF2 =>
          simp only [__smtx_dt_wf_rec] at hWf
          simp only [alignDt, native_and, Bool.and_eq_true] at hAlign
          obtain ⟨hAlignC, hAlignD⟩ := hAlign
          have hite : ∀ (b x : Bool), native_ite b x false = (b && x) := by
            intro b x; cases b <;> simp [native_ite]
          rw [hite] at hWf
          rw [Bool.and_eq_true] at hWf
          obtain ⟨hcw, hd2⟩ := hWf
          simp only [smtx_dt_context_substitute_apply, __smtx_dt_substitute]
          rw [smtx_dtc_context_substitute_no_root_of_wf_apply sub base root oldRoot newRoot c
                (refs := native_reflist_nil) (cF := cF) hcw hAlignC,
              smtx_dt_context_substitute_no_root_of_wf_apply sub base root oldRoot newRoot d2
                (refs := native_reflist_nil) (dF := dF2) hd2 hAlignD]

end

private theorem smtx_chain_type_context_substitute_no_root_of_chain_wf_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype) :
    (T : SmtType) -> {refs : RefList} ->
      smtx_type_chain_field_wf_rec refs T ->
      smtx_chain_type_context_substitute_apply sub base root oldRoot newRoot
          true false T =
        smtx_chain_type_substitute_top_apply sub base T
  | SmtType.DtcAppType A B, refs, hWf => by
      have hA : smtx_type_field_wf_rec A refs :=
        smtx_type_chain_field_wf_rec_head_of_dtc_app hWf
      have hB : smtx_type_chain_field_wf_rec refs B :=
        smtx_type_chain_field_wf_rec_tail_of_dtc_app hWf
      have hAContext :
          smtx_chain_type_context_substitute_apply
              sub base root oldRoot newRoot true false A =
            smtx_chain_type_substitute_top_apply sub base A := by
        exact smtx_chain_type_context_substitute_no_root_of_chain_wf_apply
          sub base root oldRoot newRoot A
          (smtx_type_chain_field_wf_rec_of_field_wf hA)
      have hBContext :=
        smtx_chain_type_context_substitute_no_root_of_chain_wf_apply
          sub base root oldRoot newRoot B hB
      simp [smtx_chain_type_context_substitute_apply,
        smtx_chain_type_substitute_top_apply, hAContext, hBContext]
  | SmtType.TypeRef r, refs, hWf => by
      rw [← smtx_type_context_substitute_eq_chain_type_context_substitute_apply]
      simpa [smtx_chain_type_substitute_top_apply,
        smtx_type_chain_field_wf_rec] using
        smtx_type_context_substitute_no_root_of_field_wf_apply
          sub base root oldRoot newRoot (SmtType.TypeRef r)
          (by simpa [smtx_type_chain_field_wf_rec] using hWf)
  | SmtType.Datatype s d, refs, hWf => by
      rw [← smtx_type_context_substitute_eq_chain_type_context_substitute_apply]
      simpa [smtx_chain_type_substitute_top_apply,
        smtx_type_chain_field_wf_rec] using
        smtx_type_context_substitute_no_root_of_field_wf_apply
          sub base root oldRoot newRoot (SmtType.Datatype s d)
          (by simpa [smtx_type_chain_field_wf_rec] using hWf)
  | SmtType.None, refs, hWf => by
      rw [← smtx_type_context_substitute_eq_chain_type_context_substitute_apply]
      simpa [smtx_chain_type_substitute_top_apply,
        smtx_type_chain_field_wf_rec] using
        smtx_type_context_substitute_no_root_of_field_wf_apply
          sub base root oldRoot newRoot SmtType.None
          (by simpa [smtx_type_chain_field_wf_rec] using hWf)
  | SmtType.Bool, refs, hWf => by
      rw [← smtx_type_context_substitute_eq_chain_type_context_substitute_apply]
      simpa [smtx_chain_type_substitute_top_apply,
        smtx_type_chain_field_wf_rec] using
        smtx_type_context_substitute_no_root_of_field_wf_apply
          sub base root oldRoot newRoot SmtType.Bool
          (by simpa [smtx_type_chain_field_wf_rec] using hWf)
  | SmtType.Int, refs, hWf => by
      rw [← smtx_type_context_substitute_eq_chain_type_context_substitute_apply]
      simpa [smtx_chain_type_substitute_top_apply,
        smtx_type_chain_field_wf_rec] using
        smtx_type_context_substitute_no_root_of_field_wf_apply
          sub base root oldRoot newRoot SmtType.Int
          (by simpa [smtx_type_chain_field_wf_rec] using hWf)
  | SmtType.Real, refs, hWf => by
      rw [← smtx_type_context_substitute_eq_chain_type_context_substitute_apply]
      simpa [smtx_chain_type_substitute_top_apply,
        smtx_type_chain_field_wf_rec] using
        smtx_type_context_substitute_no_root_of_field_wf_apply
          sub base root oldRoot newRoot SmtType.Real
          (by simpa [smtx_type_chain_field_wf_rec] using hWf)
  | SmtType.RegLan, refs, hWf => by
      rw [← smtx_type_context_substitute_eq_chain_type_context_substitute_apply]
      simpa [smtx_chain_type_substitute_top_apply,
        smtx_type_chain_field_wf_rec] using
        smtx_type_context_substitute_no_root_of_field_wf_apply
          sub base root oldRoot newRoot SmtType.RegLan
          (by simpa [smtx_type_chain_field_wf_rec] using hWf)
  | SmtType.BitVec w, refs, hWf => by
      rw [← smtx_type_context_substitute_eq_chain_type_context_substitute_apply]
      simpa [smtx_chain_type_substitute_top_apply,
        smtx_type_chain_field_wf_rec] using
        smtx_type_context_substitute_no_root_of_field_wf_apply
          sub base root oldRoot newRoot (SmtType.BitVec w)
          (by simpa [smtx_type_chain_field_wf_rec] using hWf)
  | SmtType.Map A B, refs, hWf => by
      rw [← smtx_type_context_substitute_eq_chain_type_context_substitute_apply]
      simpa [smtx_chain_type_substitute_top_apply,
        smtx_type_chain_field_wf_rec] using
        smtx_type_context_substitute_no_root_of_field_wf_apply
          sub base root oldRoot newRoot (SmtType.Map A B)
          (by simpa [smtx_type_chain_field_wf_rec] using hWf)
  | SmtType.Set A, refs, hWf => by
      rw [← smtx_type_context_substitute_eq_chain_type_context_substitute_apply]
      simpa [smtx_chain_type_substitute_top_apply,
        smtx_type_chain_field_wf_rec] using
        smtx_type_context_substitute_no_root_of_field_wf_apply
          sub base root oldRoot newRoot (SmtType.Set A)
          (by simpa [smtx_type_chain_field_wf_rec] using hWf)
  | SmtType.Seq A, refs, hWf => by
      rw [← smtx_type_context_substitute_eq_chain_type_context_substitute_apply]
      simpa [smtx_chain_type_substitute_top_apply,
        smtx_type_chain_field_wf_rec] using
        smtx_type_context_substitute_no_root_of_field_wf_apply
          sub base root oldRoot newRoot (SmtType.Seq A)
          (by simpa [smtx_type_chain_field_wf_rec] using hWf)
  | SmtType.Char, refs, hWf => by
      rw [← smtx_type_context_substitute_eq_chain_type_context_substitute_apply]
      simpa [smtx_chain_type_substitute_top_apply,
        smtx_type_chain_field_wf_rec] using
        smtx_type_context_substitute_no_root_of_field_wf_apply
          sub base root oldRoot newRoot SmtType.Char
          (by simpa [smtx_type_chain_field_wf_rec] using hWf)
  | SmtType.USort i, refs, hWf => by
      rw [← smtx_type_context_substitute_eq_chain_type_context_substitute_apply]
      simpa [smtx_chain_type_substitute_top_apply,
        smtx_type_chain_field_wf_rec] using
        smtx_type_context_substitute_no_root_of_field_wf_apply
          sub base root oldRoot newRoot (SmtType.USort i)
          (by simpa [smtx_type_chain_field_wf_rec] using hWf)
  | SmtType.FunType A B, refs, hWf => by
      rw [← smtx_type_context_substitute_eq_chain_type_context_substitute_apply]
      simpa [smtx_chain_type_substitute_top_apply,
        smtx_type_chain_field_wf_rec] using
        smtx_type_context_substitute_no_root_of_field_wf_apply
          sub base root oldRoot newRoot (SmtType.FunType A B)
          (by simpa [smtx_type_chain_field_wf_rec] using hWf)

private theorem smtx_ret_typeof_sel_rec_substitute_cons_apply
    (sub : native_String) (base : SmtDatatype) :
    (c : SmtDatatypeCons) -> (d : SmtDatatype) -> (j : native_Nat) ->
      __smtx_ret_typeof_sel_rec
          (SmtDatatype.sum (__smtx_dtc_substitute sub base c)
            (__smtx_dt_substitute sub base d)) native_nat_zero j =
        smtx_type_substitute_top_apply sub base
          (__smtx_ret_typeof_sel_rec (SmtDatatype.sum c d) native_nat_zero j)
  | SmtDatatypeCons.unit, d, j => by
      cases j <;>
        simp [__smtx_dtc_substitute, __smtx_ret_typeof_sel_rec,
          smtx_type_substitute_top_apply]
  | SmtDatatypeCons.cons T c, d, native_nat_zero => by
      cases T <;>
        simp [__smtx_dtc_substitute, __smtx_ret_typeof_sel_rec,
          smtx_type_substitute_top_apply, native_ite, native_streq]
  | SmtDatatypeCons.cons T c, d, native_nat_succ j => by
      cases T <;>
        simp [__smtx_dtc_substitute, __smtx_ret_typeof_sel_rec,
          smtx_ret_typeof_sel_rec_substitute_cons_apply sub base c d j]

private theorem smtx_ret_typeof_sel_rec_substitute_apply
    (sub : native_String) (base : SmtDatatype) :
    (d : SmtDatatype) -> (i j : native_Nat) ->
      __smtx_ret_typeof_sel_rec (__smtx_dt_substitute sub base d) i j =
        smtx_type_substitute_top_apply sub base
          (__smtx_ret_typeof_sel_rec d i j)
  | SmtDatatype.null, i, j => by
      cases i <;> cases j <;>
        simp [__smtx_dt_substitute, __smtx_ret_typeof_sel_rec,
          smtx_type_substitute_top_apply]
  | SmtDatatype.sum c d, native_nat_zero, j => by
      simpa [__smtx_dt_substitute] using
        smtx_ret_typeof_sel_rec_substitute_cons_apply sub base c d j
  | SmtDatatype.sum c d, native_nat_succ i, j => by
      simpa [__smtx_dt_substitute, __smtx_ret_typeof_sel_rec] using
        smtx_ret_typeof_sel_rec_substitute_apply sub base d i j

private theorem smtx_type_field_wf_rec_congr_refs_apply
    {T : SmtType} {refs refs' : RefList}
    (hEq : reflist_equiv_apply refs refs')
    (hWf : smtx_type_field_wf_rec T refs) :
    smtx_type_field_wf_rec T refs' :=
  hWf

private theorem smtx_type_chain_field_wf_rec_congr_refs_apply :
    (T : SmtType) -> {refs refs' : RefList} ->
      reflist_equiv_apply refs refs' ->
      smtx_type_chain_field_wf_rec refs T ->
      smtx_type_chain_field_wf_rec refs' T
  | SmtType.DtcAppType A B, refs, refs', hEq, hWf => by
      have hHead : smtx_type_field_wf_rec A refs :=
        smtx_type_chain_field_wf_rec_head_of_dtc_app hWf
      have hTail : smtx_type_chain_field_wf_rec refs B :=
        smtx_type_chain_field_wf_rec_tail_of_dtc_app hWf
      exact ⟨smtx_type_field_wf_rec_congr_refs_apply hEq hHead,
        smtx_type_chain_field_wf_rec_congr_refs_apply B hEq hTail⟩
  | SmtType.TypeRef r, refs, refs', hEq, hWf => by
      exact smtx_type_field_wf_rec_congr_refs_apply hEq
        (by simpa [smtx_type_chain_field_wf_rec] using hWf)
  | SmtType.Datatype s d, refs, refs', hEq, hWf => by
      exact smtx_type_field_wf_rec_congr_refs_apply hEq
        (by simpa [smtx_type_chain_field_wf_rec] using hWf)
  | SmtType.None, refs, refs', hEq, hWf => by
      exact smtx_type_field_wf_rec_congr_refs_apply hEq
        (by simpa [smtx_type_chain_field_wf_rec] using hWf)
  | SmtType.Bool, refs, refs', hEq, hWf => by
      exact smtx_type_field_wf_rec_congr_refs_apply hEq
        (by simpa [smtx_type_chain_field_wf_rec] using hWf)
  | SmtType.Int, refs, refs', hEq, hWf => by
      exact smtx_type_field_wf_rec_congr_refs_apply hEq
        (by simpa [smtx_type_chain_field_wf_rec] using hWf)
  | SmtType.Real, refs, refs', hEq, hWf => by
      exact smtx_type_field_wf_rec_congr_refs_apply hEq
        (by simpa [smtx_type_chain_field_wf_rec] using hWf)
  | SmtType.RegLan, refs, refs', hEq, hWf => by
      exact smtx_type_field_wf_rec_congr_refs_apply hEq
        (by simpa [smtx_type_chain_field_wf_rec] using hWf)
  | SmtType.BitVec w, refs, refs', hEq, hWf => by
      exact smtx_type_field_wf_rec_congr_refs_apply hEq
        (by simpa [smtx_type_chain_field_wf_rec] using hWf)
  | SmtType.Map A B, refs, refs', hEq, hWf => by
      exact smtx_type_field_wf_rec_congr_refs_apply hEq
        (by simpa [smtx_type_chain_field_wf_rec] using hWf)
  | SmtType.Set A, refs, refs', hEq, hWf => by
      exact smtx_type_field_wf_rec_congr_refs_apply hEq
        (by simpa [smtx_type_chain_field_wf_rec] using hWf)
  | SmtType.Seq A, refs, refs', hEq, hWf => by
      exact smtx_type_field_wf_rec_congr_refs_apply hEq
        (by simpa [smtx_type_chain_field_wf_rec] using hWf)
  | SmtType.Char, refs, refs', hEq, hWf => by
      exact smtx_type_field_wf_rec_congr_refs_apply hEq
        (by simpa [smtx_type_chain_field_wf_rec] using hWf)
  | SmtType.USort i, refs, refs', hEq, hWf => by
      exact smtx_type_field_wf_rec_congr_refs_apply hEq
        (by simpa [smtx_type_chain_field_wf_rec] using hWf)
  | SmtType.FunType A B, refs, refs', hEq, hWf => by
      exact smtx_type_field_wf_rec_congr_refs_apply hEq
        (by simpa [smtx_type_chain_field_wf_rec] using hWf)

/-
Substituting a fixed datatype for its recursive reference preserves datatype
well-formedness for a target datatype.

The remaining hard case is semantic rather than list-shaped: a nested datatype
field produces a fresh `native_inhabited_type` obligation for the substituted
datatype, so the proof needs inhabitance preservation for datatype substitution.
-/

private def smtx_value_dt_substitute_apply
    (sub : native_String) (base : SmtDatatype) : SmtValue -> SmtValue
  | SmtValue.DtCons s d i =>
      SmtValue.DtCons s
        (native_ite (native_streq sub s) d (__smtx_dt_substitute sub base d)) i
  | SmtValue.Apply f a =>
      match __smtx_apply_head_value f with
      | SmtValue.DtCons s _ _ =>
          native_ite (native_streq sub s) (SmtValue.Apply f a)
            (SmtValue.Apply (smtx_value_dt_substitute_apply sub base f)
              (smtx_value_dt_substitute_apply sub base a))
      | _ =>
          SmtValue.Apply (smtx_value_dt_substitute_apply sub base f)
            (smtx_value_dt_substitute_apply sub base a)
  | v => v

private theorem smtx_value_dt_substitute_apply_num_args
    (sub : native_String) (base : SmtDatatype) :
    (v : SmtValue) ->
      vsm_num_apply_args (smtx_value_dt_substitute_apply sub base v) =
        vsm_num_apply_args v
  | SmtValue.Apply f a => by
      cases hHead : __smtx_apply_head_value f
      case DtCons s d i =>
        cases hEq : native_streq sub s <;>
          simp [smtx_value_dt_substitute_apply, hHead, native_ite, hEq,
            vsm_num_apply_args, smtx_value_dt_substitute_apply_num_args sub base f]
      all_goals
        simp [smtx_value_dt_substitute_apply, hHead,
          vsm_num_apply_args, smtx_value_dt_substitute_apply_num_args sub base f]
  | SmtValue.NotValue => rfl
  | SmtValue.Boolean _ => rfl
  | SmtValue.Numeral _ => rfl
  | SmtValue.Rational _ => rfl
  | SmtValue.Binary _ _ => rfl
  | SmtValue.Map _ => rfl
  | SmtValue.Fun _ _ _ => rfl
  | SmtValue.Set _ => rfl
  | SmtValue.Seq _ => rfl
  | SmtValue.Char _ => rfl
  | SmtValue.UValue _ _ => rfl
  | SmtValue.RegLan _ => rfl
  | SmtValue.DtCons _ _ _ => rfl

private theorem smtx_value_dt_substitute_apply_head_of_dt_cons
    (sub : native_String) (base : SmtDatatype) :
    (v : SmtValue) -> {s : native_String} -> {d : SmtDatatype} -> {i : native_Nat} ->
      __smtx_apply_head_value v = SmtValue.DtCons s d i ->
      __smtx_apply_head_value (smtx_value_dt_substitute_apply sub base v) =
        SmtValue.DtCons s
          (native_ite (native_streq sub s) d (__smtx_dt_substitute sub base d)) i
  | SmtValue.DtCons s' d' i', s, d, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
      rcases hHead with ⟨rfl, hRest⟩
      rcases hRest with ⟨rfl, rfl⟩
      simp [smtx_value_dt_substitute_apply, __smtx_apply_head_value]
  | SmtValue.Apply f a, s, d, i, hHead => by
      have hHeadF : __smtx_apply_head_value f = SmtValue.DtCons s d i := by
        simpa [__smtx_apply_head_value] using hHead
      have hRec :=
        smtx_value_dt_substitute_apply_head_of_dt_cons sub base f hHeadF
      cases hEq : native_streq sub s <;>
        simp [smtx_value_dt_substitute_apply, __smtx_apply_head_value, hHeadF,
          native_ite, hEq, hRec]
  | SmtValue.NotValue, s, d, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Boolean _, s, d, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Numeral _, s, d, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Rational _, s, d, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Binary _ _, s, d, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Map _, s, d, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Fun _ _ _, s, d, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Set _, s, d, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Seq _, s, d, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Char _, s, d, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.UValue _ _, s, d, i, hHead => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.RegLan _, s, d, i, hHead => by
      simp [__smtx_apply_head_value] at hHead

private theorem smtx_value_dt_substitute_apply_arg_nth
    (sub : native_String) (base : SmtDatatype) :
    (v : SmtValue) -> (j : native_Nat) ->
      (∀ {s : native_String} {d : SmtDatatype} {i : native_Nat},
        __smtx_apply_head_value v = SmtValue.DtCons s d i -> s ≠ sub) ->
      __smtx_apply_arg_nth_value (smtx_value_dt_substitute_apply sub base v) j
          (vsm_num_apply_args (smtx_value_dt_substitute_apply sub base v)) =
        smtx_value_dt_substitute_apply sub base
          (__smtx_apply_arg_nth_value v j (vsm_num_apply_args v))
  | SmtValue.Apply f a, j, hNoShadow => by
      have hNoShadowF :
          ∀ {s : native_String} {d : SmtDatatype} {i : native_Nat},
            __smtx_apply_head_value f = SmtValue.DtCons s d i -> s ≠ sub := by
        intro s d i hHead
        exact hNoShadow (by simpa [__smtx_apply_head_value] using hHead)
      cases hHead : __smtx_apply_head_value f
      case DtCons s d i =>
        have hNe : s ≠ sub := hNoShadowF hHead
        have hStreq : native_streq sub s = false := by
          cases hEq : native_streq sub s <;> simp [native_streq] at hEq ⊢
          exact False.elim (hNe hEq.symm)
        by_cases hEq : native_nateq j (vsm_num_apply_args f) = true
        · simp [smtx_value_dt_substitute_apply, hHead, __smtx_apply_arg_nth_value,
            vsm_num_apply_args, native_ite, hStreq,
            smtx_value_dt_substitute_apply_num_args sub base f, hEq]
        · have hArg := smtx_value_dt_substitute_apply_arg_nth sub base f j hNoShadowF
          simp [smtx_value_dt_substitute_apply, hHead, __smtx_apply_arg_nth_value,
            vsm_num_apply_args, native_ite, hStreq,
            smtx_value_dt_substitute_apply_num_args sub base f, hEq]
          simpa [smtx_value_dt_substitute_apply_num_args sub base f] using hArg
      all_goals
        by_cases hEq : native_nateq j (vsm_num_apply_args f) = true
        · simp [smtx_value_dt_substitute_apply, hHead, __smtx_apply_arg_nth_value,
            vsm_num_apply_args, native_ite,
            smtx_value_dt_substitute_apply_num_args sub base f, hEq]
        · have hArg := smtx_value_dt_substitute_apply_arg_nth sub base f j hNoShadowF
          simp [smtx_value_dt_substitute_apply, hHead, __smtx_apply_arg_nth_value,
            vsm_num_apply_args, native_ite,
            smtx_value_dt_substitute_apply_num_args sub base f, hEq]
          simpa [smtx_value_dt_substitute_apply_num_args sub base f] using hArg
  | SmtValue.NotValue, _, _ => rfl
  | SmtValue.Boolean _, _, _ => rfl
  | SmtValue.Numeral _, _, _ => rfl
  | SmtValue.Rational _, _, _ => rfl
  | SmtValue.Binary _ _, _, _ => rfl
  | SmtValue.Map _, _, _ => rfl
  | SmtValue.Fun _ _ _, _, _ => rfl
  | SmtValue.Set _, _, _ => rfl
  | SmtValue.Seq _, _, _ => rfl
  | SmtValue.Char _, _, _ => rfl
  | SmtValue.UValue _ _, _, _ => rfl
  | SmtValue.RegLan _, _, _ => rfl
  | SmtValue.DtCons _ _ _, _, _ => rfl

private theorem smtx_value_dtc_app_type_head_exists_apply :
    (v : SmtValue) -> {A B : SmtType} ->
      __smtx_typeof_value v = SmtType.DtcAppType A B ->
      ∃ s d i, __smtx_apply_head_value v = SmtValue.DtCons s d i
  | SmtValue.NotValue, A, B, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.Boolean _, A, B, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.Numeral _, A, B, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.Rational _, A, B, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.Binary w n, A, B, h => by
      cases hWidth : native_zleq 0 w <;>
        cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_typeof_value, native_ite, SmtEval.native_and, hWidth, hMod] at h
  | SmtValue.Map m, A, B, h => by
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨T, U, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | SmtValue.Fun _ _ _, A, B, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.Set m, A, B, h => by
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨T, U, hMap⟩
          cases U <;>
            simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_set_type, hNone] at h
  | SmtValue.Seq ss, A, B, h => by
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨T, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | SmtValue.Char c, A, B, h => by
      cases hValid : native_char_valid c <;>
        simp [__smtx_typeof_value, SmtEval.native_ite, hValid] at h
  | SmtValue.UValue _ _, A, B, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.RegLan _, A, B, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.DtCons s d i, A, B, h => by
      exact ⟨s, d, i, rfl⟩
  | SmtValue.Apply f a, A, B, h => by
      change
        __smtx_typeof_apply_value (__smtx_typeof_value f) (__smtx_typeof_value a) =
          SmtType.DtcAppType A B at h
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_apply_value, hf] at h
      case DtcAppType C D =>
        rcases smtx_value_dtc_app_type_head_exists_apply f hf with
          ⟨s, d, i, hHead⟩
        exact ⟨s, d, i, by simpa [__smtx_apply_head_value] using hHead⟩

private def smtx_type_fun_like_domains_no_reglan : SmtType -> Prop
  | SmtType.Seq A => smtx_type_fun_like_domains_no_reglan A
  | SmtType.Set A => smtx_type_fun_like_domains_no_reglan A
  | SmtType.Map A B =>
      smtx_type_fun_like_domains_no_reglan A ∧
        smtx_type_fun_like_domains_no_reglan B
  | SmtType.FunType A B =>
      A ≠ SmtType.RegLan ∧
        smtx_type_fun_like_domains_no_reglan A ∧
          smtx_type_fun_like_domains_no_reglan B
  | SmtType.DtcAppType A B =>
      A ≠ SmtType.RegLan ∧
        smtx_type_fun_like_domains_no_reglan A ∧
          smtx_type_fun_like_domains_no_reglan B
  | _ => True

private def smtx_type_fun_like_domains_field_wf : SmtType -> Prop
  | SmtType.Seq A => smtx_type_fun_like_domains_field_wf A
  | SmtType.Set A => smtx_type_fun_like_domains_field_wf A
  | SmtType.Map A B =>
      smtx_type_fun_like_domains_field_wf A ∧
        smtx_type_fun_like_domains_field_wf B
  | SmtType.FunType A B =>
      smtx_type_field_wf_rec A native_reflist_nil ∧
        smtx_type_fun_like_domains_field_wf A ∧
          smtx_type_fun_like_domains_field_wf B
  | SmtType.DtcAppType A B =>
      smtx_type_field_wf_rec A native_reflist_nil ∧
        smtx_type_fun_like_domains_field_wf A ∧
          smtx_type_fun_like_domains_field_wf B
  | _ => True

private theorem smtx_type_fun_like_domains_field_wf_of_type_wf_rec :
    ∀ {F T : SmtType},
      __smtx_type_wf_rec F T = true ->
        smtx_type_fun_like_domains_field_wf T
  | _, SmtType.None, h => by
      simp [__smtx_type_wf_rec] at h
  | _, SmtType.Bool, _h => by
      simp [smtx_type_fun_like_domains_field_wf]
  | _, SmtType.Int, _h => by
      simp [smtx_type_fun_like_domains_field_wf]
  | _, SmtType.Real, _h => by
      simp [smtx_type_fun_like_domains_field_wf]
  | _, SmtType.RegLan, h => by
      simp [__smtx_type_wf_rec] at h
  | _, SmtType.BitVec _w, _h => by
      simp [smtx_type_fun_like_domains_field_wf]
  | _, SmtType.Map A B, h => by
      have h' : __smtx_type_wf_rec (SmtType.Map A B) (SmtType.Map A B) = true := by
        simpa [__smtx_type_wf_rec] using h
      rcases map_type_wf_rec_components_of_wf h' with ⟨hA, hB⟩
      exact ⟨smtx_type_fun_like_domains_field_wf_of_type_wf_rec (F := A) (T := A) hA,
        smtx_type_fun_like_domains_field_wf_of_type_wf_rec (F := B) (T := B) hB⟩
  | _, SmtType.Set A, h => by
      have h' : __smtx_type_wf_rec (SmtType.Set A) (SmtType.Set A) = true := by
        simpa [__smtx_type_wf_rec] using h
      exact smtx_type_fun_like_domains_field_wf_of_type_wf_rec (F := A) (T := A)
        (set_type_wf_rec_component_of_wf h')
  | _, SmtType.Seq A, h => by
      have h' : __smtx_type_wf_rec (SmtType.Seq A) (SmtType.Seq A) = true := by
        simpa [__smtx_type_wf_rec] using h
      exact smtx_type_fun_like_domains_field_wf_of_type_wf_rec (F := A) (T := A)
        (seq_type_wf_rec_component_of_wf h')
  | _, SmtType.Char, _h => by
      simp [smtx_type_fun_like_domains_field_wf]
  | _, SmtType.Datatype _s _d, _h => by
      simp [smtx_type_fun_like_domains_field_wf]
  | _, SmtType.TypeRef _s, _h => by
      simp [smtx_type_fun_like_domains_field_wf]
  | _, SmtType.USort _i, _h => by
      simp [smtx_type_fun_like_domains_field_wf]
  | _, SmtType.FunType A B, h => by
      simp [__smtx_type_wf_rec] at h
  | _, SmtType.DtcAppType _A _B, h => by
      simp [__smtx_type_wf_rec] at h
termination_by F T h => sizeOf T
decreasing_by
  all_goals simp_wf
  all_goals simp [sizeOf]
  all_goals omega

private theorem smtx_type_fun_like_domains_field_wf_of_field_wf_rec
    {T : SmtType} {refs : RefList}
    (h : smtx_type_field_wf_rec T refs) :
    smtx_type_fun_like_domains_field_wf T := by
  cases T
  case TypeRef _s => simp [smtx_type_fun_like_domains_field_wf]
  all_goals
    exact smtx_type_fun_like_domains_field_wf_of_type_wf_rec (by
      simpa [smtx_type_field_wf_rec] using h)

private theorem smtx_type_fun_like_domains_field_wf_of_chain_field_wf_rec :
    (T : SmtType) ->
      smtx_type_chain_field_wf_rec native_reflist_nil T ->
        smtx_type_fun_like_domains_field_wf T
  | SmtType.DtcAppType A B, hWF => by
      have hA : smtx_type_field_wf_rec A native_reflist_nil :=
        smtx_type_chain_field_wf_rec_head_of_dtc_app hWF
      have hB : smtx_type_chain_field_wf_rec native_reflist_nil B :=
        smtx_type_chain_field_wf_rec_tail_of_dtc_app hWF
      exact ⟨hA, smtx_type_fun_like_domains_field_wf_of_field_wf_rec hA,
        smtx_type_fun_like_domains_field_wf_of_chain_field_wf_rec B hB⟩
  | SmtType.TypeRef r, hWF => by
      exact smtx_type_fun_like_domains_field_wf_of_field_wf_rec
        (by simpa [smtx_type_chain_field_wf_rec] using hWF)
  | SmtType.Datatype s d, hWF => by
      exact smtx_type_fun_like_domains_field_wf_of_field_wf_rec
        (by simpa [smtx_type_chain_field_wf_rec] using hWF)
  | SmtType.None, hWF => by
      exact smtx_type_fun_like_domains_field_wf_of_field_wf_rec
        (by simpa [smtx_type_chain_field_wf_rec] using hWF)
  | SmtType.Bool, hWF => by
      exact smtx_type_fun_like_domains_field_wf_of_field_wf_rec
        (by simpa [smtx_type_chain_field_wf_rec] using hWF)
  | SmtType.Int, hWF => by
      exact smtx_type_fun_like_domains_field_wf_of_field_wf_rec
        (by simpa [smtx_type_chain_field_wf_rec] using hWF)
  | SmtType.Real, hWF => by
      exact smtx_type_fun_like_domains_field_wf_of_field_wf_rec
        (by simpa [smtx_type_chain_field_wf_rec] using hWF)
  | SmtType.RegLan, hWF => by
      exact smtx_type_fun_like_domains_field_wf_of_field_wf_rec
        (by simpa [smtx_type_chain_field_wf_rec] using hWF)
  | SmtType.BitVec w, hWF => by
      exact smtx_type_fun_like_domains_field_wf_of_field_wf_rec
        (by simpa [smtx_type_chain_field_wf_rec] using hWF)
  | SmtType.Map A B, hWF => by
      exact smtx_type_fun_like_domains_field_wf_of_field_wf_rec
        (by simpa [smtx_type_chain_field_wf_rec] using hWF)
  | SmtType.Set A, hWF => by
      exact smtx_type_fun_like_domains_field_wf_of_field_wf_rec
        (by simpa [smtx_type_chain_field_wf_rec] using hWF)
  | SmtType.Seq A, hWF => by
      exact smtx_type_fun_like_domains_field_wf_of_field_wf_rec
        (by simpa [smtx_type_chain_field_wf_rec] using hWF)
  | SmtType.Char, hWF => by
      exact smtx_type_fun_like_domains_field_wf_of_field_wf_rec
        (by simpa [smtx_type_chain_field_wf_rec] using hWF)
  | SmtType.USort i, hWF => by
      exact smtx_type_fun_like_domains_field_wf_of_field_wf_rec
        (by simpa [smtx_type_chain_field_wf_rec] using hWF)
  | SmtType.FunType A B, hWF => by
      exact smtx_type_fun_like_domains_field_wf_of_field_wf_rec
        (by simpa [smtx_type_chain_field_wf_rec] using hWF)
termination_by T hWF => sizeOf T
decreasing_by
  all_goals simp_wf
  all_goals simp [sizeOf]
  all_goals omega

private theorem smtx_type_fun_like_domains_no_reglan_of_type_wf_rec :
    ∀ {F T : SmtType},
      __smtx_type_wf_rec F T = true ->
        smtx_type_fun_like_domains_no_reglan T
  | _, SmtType.None, h => by
      simp [__smtx_type_wf_rec] at h
  | _, SmtType.Bool, _h => by
      simp [smtx_type_fun_like_domains_no_reglan]
  | _, SmtType.Int, _h => by
      simp [smtx_type_fun_like_domains_no_reglan]
  | _, SmtType.Real, _h => by
      simp [smtx_type_fun_like_domains_no_reglan]
  | _, SmtType.RegLan, h => by
      simp [__smtx_type_wf_rec] at h
  | _, SmtType.BitVec _w, _h => by
      simp [smtx_type_fun_like_domains_no_reglan]
  | _, SmtType.Map A B, h => by
      have h' : __smtx_type_wf_rec (SmtType.Map A B) (SmtType.Map A B) = true := by
        simpa [__smtx_type_wf_rec] using h
      rcases map_type_wf_rec_components_of_wf h' with ⟨hA, hB⟩
      exact ⟨smtx_type_fun_like_domains_no_reglan_of_type_wf_rec (F := A) (T := A) hA,
        smtx_type_fun_like_domains_no_reglan_of_type_wf_rec (F := B) (T := B) hB⟩
  | _, SmtType.Set A, h => by
      have h' : __smtx_type_wf_rec (SmtType.Set A) (SmtType.Set A) = true := by
        simpa [__smtx_type_wf_rec] using h
      exact smtx_type_fun_like_domains_no_reglan_of_type_wf_rec (F := A) (T := A)
        (set_type_wf_rec_component_of_wf h')
  | _, SmtType.Seq A, h => by
      have h' : __smtx_type_wf_rec (SmtType.Seq A) (SmtType.Seq A) = true := by
        simpa [__smtx_type_wf_rec] using h
      exact smtx_type_fun_like_domains_no_reglan_of_type_wf_rec (F := A) (T := A)
        (seq_type_wf_rec_component_of_wf h')
  | _, SmtType.Char, _h => by
      simp [smtx_type_fun_like_domains_no_reglan]
  | _, SmtType.Datatype _s _d, _h => by
      simp [smtx_type_fun_like_domains_no_reglan]
  | _, SmtType.TypeRef _s, h => by
      simp [__smtx_type_wf_rec] at h
  | _, SmtType.USort _i, _h => by
      simp [smtx_type_fun_like_domains_no_reglan]
  | _, SmtType.FunType A B, h => by
      simp [__smtx_type_wf_rec] at h
  | _, SmtType.DtcAppType _A _B, h => by
      simp [__smtx_type_wf_rec] at h
termination_by F T h => sizeOf T
decreasing_by
  all_goals simp_wf
  all_goals simp [sizeOf]
  all_goals omega

private theorem smtx_type_fun_like_domains_no_reglan_of_type_wf
    {T : SmtType} (h : __smtx_type_wf T = true) :
    smtx_type_fun_like_domains_no_reglan T := by
  by_cases hReg : T = SmtType.RegLan
  · subst T
    simp [smtx_type_fun_like_domains_no_reglan]
  · by_cases hFun : ∃ A B : SmtType, T = SmtType.FunType A B
    · rcases hFun with ⟨A, B, rfl⟩
      rcases fun_type_wf_rec_components_of_wf h with ⟨hA, hB⟩
      exact ⟨
        smtx_type_field_wf_rec_ne_reglan
          (smtx_type_field_wf_rec_of_type_wf_rec (refs := native_reflist_nil) hA),
        smtx_type_fun_like_domains_no_reglan_of_type_wf_rec (F := A) (T := A) hA,
        smtx_type_fun_like_domains_no_reglan_of_type_wf_rec (F := B) (T := B) hB⟩
    · exact smtx_type_fun_like_domains_no_reglan_of_type_wf_rec (F := T) (T := T)
        (smtx_type_wf_rec_of_type_wf hReg
          (by
            intro A B hEq
            exact hFun ⟨A, B, hEq⟩)
          (by
            intro A B hEq
            exact hFun ⟨A, B, hEq⟩)
          h)

private theorem smtx_type_fun_like_arg_ne_reglan_of_no_reglan
    {T A B : SmtType}
    (hWF : smtx_type_fun_like_domains_no_reglan T)
    (hHead : T = SmtType.FunType A B ∨ T = SmtType.DtcAppType A B) :
    A ≠ SmtType.RegLan := by
  rcases hHead with hHead | hHead
  · rw [hHead] at hWF
    exact hWF.1
  · rw [hHead] at hWF
    exact hWF.1

private theorem smtx_type_fun_like_domains_no_reglan_apply
    {F X : SmtType}
    (hF : smtx_type_fun_like_domains_no_reglan F)
    (hNN : __smtx_typeof_apply F X ≠ SmtType.None) :
    smtx_type_fun_like_domains_no_reglan (__smtx_typeof_apply F X) := by
  rcases typeof_apply_non_none_cases hNN with ⟨A, B, hHead, hX, hA, _hB⟩
  have hRes : __smtx_typeof_apply F X = B :=
    smtx_typeof_apply_of_head_cases hHead hX hA
  rw [hRes]
  rcases hHead with hHead | hHead
  · rw [hHead] at hF
    exact hF.2.2
  · rw [hHead] at hF
    exact hF.2.2

private def smtx_dtc_substitute_field_type
    (s : native_String) (base : SmtDatatype) : SmtType -> SmtType
  | SmtType.Datatype s2 d2 =>
      SmtType.Datatype s2
        (native_ite (native_streq s s2) d2 (__smtx_dt_substitute s (__smtx_dt_lift s2 d2 base) d2))
  | SmtType.TypeRef s2 =>
      native_ite (native_streq s s2) (SmtType.Datatype s base) (SmtType.TypeRef s2)
  | T => T

/-- A recursively well-formed type has no `RegLan` at any fun-like (function/`DtcApp`) domain, and
is not itself `RegLan`. Well-formedness rejects `RegLan` at every field/component position
(`__smtx_type_wf_rec _ RegLan = false`), so it can never appear anywhere `no_reglan` inspects. The
"full" side `UF` is irrelevant: for every shape `no_reglan` recurses into, `wf_rec` ignores it. -/
private theorem smtx_type_fun_like_domains_no_reglan_of_wf_rec :
    (U : SmtType) → (UF : SmtType) → __smtx_type_wf_rec UF U = true →
      U ≠ SmtType.RegLan ∧ smtx_type_fun_like_domains_no_reglan U
  | SmtType.Map A B, UF, h => by
      have hParts :
          ((native_inhabited_type A = true ∧ __smtx_type_wf_rec A A = true) ∧
            __smtx_type_no_alias_rec native_reflist_nil A = true) ∧
            (native_inhabited_type B = true ∧ __smtx_type_wf_rec B B = true) ∧
              __smtx_type_no_alias_rec native_reflist_nil B = true := by
        simpa [__smtx_type_wf_rec, native_and] using h
      have hA := smtx_type_fun_like_domains_no_reglan_of_wf_rec A A hParts.1.1.2
      have hB := smtx_type_fun_like_domains_no_reglan_of_wf_rec B B hParts.2.1.2
      exact ⟨by simp, hA.2, hB.2⟩
  | SmtType.Set A, UF, h => by
      have hA' : (native_inhabited_type A = true ∧ __smtx_type_wf_rec A A = true) ∧
          __smtx_type_no_alias_rec native_reflist_nil A = true := by
        simpa [__smtx_type_wf_rec, native_and] using h
      have hA := smtx_type_fun_like_domains_no_reglan_of_wf_rec A A hA'.1.2
      exact ⟨by simp, hA.2⟩
  | SmtType.Seq A, UF, h => by
      have hA' : (native_inhabited_type A = true ∧ __smtx_type_wf_rec A A = true) ∧
          __smtx_type_no_alias_rec native_reflist_nil A = true := by
        simpa [__smtx_type_wf_rec, native_and] using h
      have hA := smtx_type_fun_like_domains_no_reglan_of_wf_rec A A hA'.1.2
      exact ⟨by simp, hA.2⟩
  | SmtType.RegLan, UF, h => by simp [__smtx_type_wf_rec] at h
  | SmtType.FunType A B, UF, h => by simp [__smtx_type_wf_rec] at h
  | SmtType.DtcAppType A B, UF, h => by simp [__smtx_type_wf_rec] at h
  | SmtType.None, UF, h => by simp [__smtx_type_wf_rec] at h
  | SmtType.TypeRef s, UF, h => by simp [__smtx_type_wf_rec] at h
  | SmtType.Datatype s d, UF, h => ⟨by simp, trivial⟩
  | SmtType.Bool, UF, h => ⟨by simp, trivial⟩
  | SmtType.Int, UF, h => ⟨by simp, trivial⟩
  | SmtType.Real, UF, h => ⟨by simp, trivial⟩
  | SmtType.BitVec n, UF, h => ⟨by simp, trivial⟩
  | SmtType.Char, UF, h => ⟨by simp, trivial⟩
  | SmtType.USort i, UF, h => ⟨by simp, trivial⟩
  termination_by U => sizeOf U

/-- The head field of a well-formed constructor whose (unfolded) head is not a bare `TypeRef` is
recursively well-formed against its full-side counterpart (the non-`TypeRef` second clause of
`__smtx_dt_cons_wf_rec`). -/
private theorem smtx_cons_wf_head_wf_rec
    (UF U : SmtType) (cFtl c : SmtDatatypeCons)
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
  by_cases hcond :
      native_and (native_inhabited_type UF) (__smtx_type_wf_rec UF U) = true
  · simp only [native_and, Bool.and_eq_true] at hcond; exact hcond.2
  · rw [native_ite, if_neg (by simpa using hcond)] at h
    exact absurd h (by simp)

/-- Substituting a field type preserves "not `RegLan`, and no fun-like `RegLan` domain": the
`Datatype`/`TypeRef` shapes map to `Datatype`/`TypeRef` (both `no_reglan`-trivial), and every other
shape is left untouched, where the field's own well-formedness (extracted from the constructor
well-formedness) supplies the `no_reglan` fact via `smtx_type_fun_like_domains_no_reglan_of_wf_rec`. -/
private theorem smtx_dtc_substitute_field_no_reglan_of_cons_wf
    (s : native_String) (base : SmtDatatype) {U : SmtType}
    {c cF : SmtDatatypeCons} {refs : RefList}
    (hCons : __smtx_dt_cons_wf_rec cF (SmtDatatypeCons.cons U c) = true) :
    smtx_dtc_substitute_field_type s base U ≠ SmtType.RegLan ∧
    smtx_type_fun_like_domains_no_reglan
      (smtx_dtc_substitute_field_type s base U) := by
  cases cF with
  | unit =>
      -- a `unit` full side is never constructor-well-formed against a `cons` field.
      simp [__smtx_dt_cons_wf_rec] at hCons
  | cons UF cFtl =>
      by_cases hRef : ∃ s2, U = SmtType.TypeRef s2
      · -- `TypeRef` field: substitution yields a `Datatype`/`TypeRef`, both `no_reglan`-trivial.
        obtain ⟨s2, rfl⟩ := hRef
        by_cases hst : native_streq s s2 = true <;>
          (refine ⟨?_, ?_⟩ <;>
            simp [smtx_dtc_substitute_field_type, native_ite, hst,
              smtx_type_fun_like_domains_no_reglan])
      · -- non-`TypeRef` field: constructor well-formedness uses the second `dt_cons_wf_rec` clause,
        -- giving `wf_rec UF U`, which forbids `RegLan` at every `no_reglan` position.
        have hUwf : __smtx_type_wf_rec UF U = true :=
          smtx_cons_wf_head_wf_rec UF U cFtl c (fun s2 he => hRef ⟨s2, he⟩) hCons
        by_cases hDt : ∃ s2 d2, U = SmtType.Datatype s2 d2
        · obtain ⟨s2, d2, rfl⟩ := hDt
          refine ⟨?_, ?_⟩ <;>
            simp [smtx_dtc_substitute_field_type, native_ite,
              smtx_type_fun_like_domains_no_reglan]
        · have hEq : smtx_dtc_substitute_field_type s base U = U := by
            cases U <;> simp_all [smtx_dtc_substitute_field_type]
          rw [hEq]
          exact smtx_type_fun_like_domains_no_reglan_of_wf_rec U UF hUwf

private theorem smtx_typeof_dt_cons_rec_no_reglan_of_substitute_wf
    (s : native_String) (base : SmtDatatype) :
    ∀ (d dF d0 : SmtDatatype) (i : native_Nat) (refs : RefList),
      __smtx_dt_wf_rec dF d = true ->
      smtx_type_fun_like_domains_no_reglan
        (__smtx_typeof_dt_cons_rec (SmtType.Datatype s d0)
          (__smtx_dt_substitute s base d) i)
  | SmtDatatype.null, dF, d0, i, refs, hWf => by
      -- `subst null = null`, whose `typeof_dt_cons_rec` is `None` (`no_reglan None = True`).
      cases i <;>
        simp [__smtx_dt_substitute, __smtx_typeof_dt_cons_rec,
          smtx_type_fun_like_domains_no_reglan]
  | SmtDatatype.sum c dtl, dF, d0, native_nat_zero, refs, hWf => by
      cases dF with
      | null => simp [__smtx_dt_wf_rec] at hWf
      | sum cF dFtl =>
          have hParts : __smtx_dt_cons_wf_rec cF c = true ∧ __smtx_dt_wf_rec dFtl dtl = true := by
            by_cases hc : __smtx_dt_cons_wf_rec cF c = true
            · refine ⟨hc, ?_⟩
              simp only [__smtx_dt_wf_rec, native_ite, if_pos hc] at hWf
              exact hWf
            · rw [__smtx_dt_wf_rec, native_ite, if_neg (by simpa using hc)] at hWf
              exact absurd hWf (by simp)
          cases c with
          | unit =>
              -- constructor with no fields: the chain is just the base datatype (`no_reglan` trivial).
              simp [__smtx_dt_substitute, __smtx_dtc_substitute, __smtx_typeof_dt_cons_rec,
                smtx_type_fun_like_domains_no_reglan]
          | cons U c' =>
              cases cF with
              | unit => exact absurd hParts.1 (by simp [__smtx_dt_cons_wf_rec])
              | cons UF cFtl' =>
                  -- head field `U` gives `DtcAppType (subst-field U) (chain over the tail)`.
                  have hHead :
                      smtx_dtc_substitute_field_type s base U ≠ SmtType.RegLan ∧
                      smtx_type_fun_like_domains_no_reglan (smtx_dtc_substitute_field_type s base U) :=
                    smtx_dtc_substitute_field_no_reglan_of_cons_wf (refs := native_reflist_nil)
                      s base hParts.1
                  have hTailCons : __smtx_dt_cons_wf_rec cFtl' c' = true :=
                    smtx_dt_cons_wf_rec_tail_of_true hParts.1
                  have hTailWf :
                      __smtx_dt_wf_rec (SmtDatatype.sum cFtl' dFtl) (SmtDatatype.sum c' dtl) = true := by
                    simp only [__smtx_dt_wf_rec, native_ite, if_pos hTailCons]
                    exact hParts.2
                  have hTail :=
                    smtx_typeof_dt_cons_rec_no_reglan_of_substitute_wf s base
                      (SmtDatatype.sum c' dtl) (SmtDatatype.sum cFtl' dFtl) d0
                      native_nat_zero refs hTailWf
                  -- reduce the goal's chain to `DtcAppType (subst-field U) (tail chain)`.
                  have hFieldEq :
                      __smtx_type_substitute s base U = smtx_dtc_substitute_field_type s base U := by
                    cases U <;> rfl
                  simp only [__smtx_dt_substitute, __smtx_dtc_substitute, __smtx_typeof_dt_cons_rec,
                    hFieldEq, smtx_type_fun_like_domains_no_reglan]
                  exact ⟨hHead.1, hHead.2, hTail⟩
  | SmtDatatype.sum c dtl, dF, d0, native_nat_succ n, refs, hWf => by
      cases dF with
      | null => simp [__smtx_dt_wf_rec] at hWf
      | sum cF dFtl =>
          have hDtlWf : __smtx_dt_wf_rec dFtl dtl = true := by
            by_cases hc : __smtx_dt_cons_wf_rec cF c = true
            · simp only [__smtx_dt_wf_rec, native_ite, if_pos hc] at hWf; exact hWf
            · rw [__smtx_dt_wf_rec, native_ite, if_neg (by simpa using hc)] at hWf
              exact absurd hWf (by simp)
          have hRec :=
            smtx_typeof_dt_cons_rec_no_reglan_of_substitute_wf s base dtl dFtl d0 n refs hDtlWf
          -- `typeof_dt_cons_rec … (subst (sum c dtl)) (succ n) = typeof_dt_cons_rec … (subst dtl) n`.
          simp only [__smtx_dt_substitute, __smtx_typeof_dt_cons_rec]
          exact hRec
  termination_by d _ _ _ _ _ => sizeOf d

private theorem smtx_typeof_dt_cons_no_reglan_of_non_none
    (s : native_String) (d : SmtDatatype) (i : native_Nat)
    (hNN : term_has_non_none_type (SmtTerm.DtCons s d i)) :
    smtx_type_fun_like_domains_no_reglan
      (__smtx_typeof (SmtTerm.DtCons s d i)) := by
  let raw := __smtx_typeof_dt_cons_rec (SmtType.Datatype s d) (__smtx_dt_substitute s d d) i
  have hGuardNN : __smtx_typeof_guard_wf (SmtType.Datatype s d) raw ≠ SmtType.None := by
    unfold term_has_non_none_type at hNN
    simpa [Smtm.typeof_dt_cons_eq, raw] using hNN
  have hRawEq : __smtx_typeof (SmtTerm.DtCons s d i) = raw := by
    rw [Smtm.typeof_dt_cons_eq]
    exact smtx_typeof_guard_wf_of_non_none (SmtType.Datatype s d) raw hGuardNN
  have hBaseTypeWf : __smtx_type_wf (SmtType.Datatype s d) = true :=
    Smtm.smtx_typeof_guard_wf_wf_of_non_none (SmtType.Datatype s d) raw hGuardNN
  have hBaseWf : __smtx_dt_wf_rec (__smtx_dt_substitute s d d) d = true :=
    datatype_wf_rec_of_type_wf hBaseTypeWf
  rw [hRawEq]
  exact smtx_typeof_dt_cons_rec_no_reglan_of_substitute_wf
    s d d (__smtx_dt_substitute s d d) d i native_reflist_nil hBaseWf

private theorem smtx_typeof_apply_dt_sel_no_reglan_of_non_none
    (s : native_String) (d : SmtDatatype) (i j : native_Nat) (x : SmtTerm)
    (hNN : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)) :
    smtx_type_fun_like_domains_no_reglan
      (__smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)) := by
  let R := __smtx_ret_typeof_sel s d i j
  let inner :=
    __smtx_typeof_apply (SmtType.FunType (SmtType.Datatype s d) R) (__smtx_typeof x)
  have hGuardNN : __smtx_typeof_guard_wf R inner ≠ SmtType.None := by
    unfold term_has_non_none_type at hNN
    rw [typeof_dt_sel_apply_eq] at hNN
    simpa [R, inner] using hNN
  have hTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s d i j) x) = R := by
    simpa [R] using dt_sel_term_typeof_of_non_none hNN
  have hWF : __smtx_type_wf R = true :=
    Smtm.smtx_typeof_guard_wf_wf_of_non_none R inner hGuardNN
  rw [hTy]
  exact smtx_type_fun_like_domains_no_reglan_of_type_wf hWF

private theorem choice_nth_fun_like_domains_no_reglan_any
    (s : native_String) (T : SmtType) (body : SmtTerm)
    (hNN : term_has_non_none_type (SmtTerm.choice s T body)) :
    smtx_type_fun_like_domains_no_reglan (__smtx_typeof (SmtTerm.choice s T body)) := by
  have hGuardTy :
      __smtx_typeof (SmtTerm.choice s T body) = __smtx_typeof_guard_wf T T :=
    Smtm.choice_term_guard_type_of_non_none hNN
  have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    intro hNone
    unfold term_has_non_none_type at hNN
    rw [hGuardTy, hNone] at hNN
    exact hNN rfl
  have hWf : __smtx_type_wf T = true :=
    Smtm.smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
  have hTy : __smtx_typeof (SmtTerm.choice s T body) = T :=
    Smtm.choice_term_typeof_of_non_none hNN
  rw [hTy]
  exact smtx_type_fun_like_domains_no_reglan_of_type_wf hWf

private theorem smtx_term_has_non_none_of_type_eq_no_reglan
    {t : SmtTerm} {T : SmtType}
    (h : __smtx_typeof t = T)
    (hT : T ≠ SmtType.None) :
    term_has_non_none_type t := by
  unfold term_has_non_none_type
  rw [h]
  exact hT

theorem smtx_term_fun_like_arg_ne_reglan_of_non_none :
    ∀ (t : SmtTerm), term_has_non_none_type t ->
      ∀ {A B : SmtType},
        (__smtx_typeof t = SmtType.FunType A B ∨
          __smtx_typeof t = SmtType.DtcAppType A B) ->
        A ≠ SmtType.RegLan := by
  let rec go (t : SmtTerm) (hNN : term_has_non_none_type t) :
      smtx_type_fun_like_domains_no_reglan (__smtx_typeof t) := by
    cases t
    case Apply f x =>
        by_cases hSel : ∃ s d i j, f = SmtTerm.DtSel s d i j
        · rcases hSel with ⟨s, d, i, j, rfl⟩
          exact smtx_typeof_apply_dt_sel_no_reglan_of_non_none s d i j x hNN
        · by_cases hTester : ∃ s d i, f = SmtTerm.DtTester s d i
          · rcases hTester with ⟨s, d, i, rfl⟩
            have hTy :
                __smtx_typeof (SmtTerm.Apply (SmtTerm.DtTester s d i) x) =
                  SmtType.Bool :=
              dt_tester_term_typeof_of_non_none hNN
            rw [hTy]
            simp [smtx_type_fun_like_domains_no_reglan]
          · have hGeneric :
                generic_apply_type f x :=
              generic_apply_type_of_non_special_head f x
                (by
                  intro s d i j h
                  exact hSel ⟨s, d, i, j, h⟩)
                (by
                  intro s d i h
                  exact hTester ⟨s, d, i, h⟩)
            have hApplyNN :
                __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None := by
              unfold term_has_non_none_type at hNN
              rw [hGeneric] at hNN
              exact hNN
            have hFNN : term_has_non_none_type f := by
              rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, _hX, _hA, _hB⟩
              unfold term_has_non_none_type
              exact smtx_head_non_none_of_apply_cases hHead
            rw [hGeneric]
            exact smtx_type_fun_like_domains_no_reglan_apply (go f hFNN) hApplyNN
    case Var s T =>
        have hWf : __smtx_type_wf T = true :=
          Smtm.smtx_typeof_guard_wf_wf_of_non_none T T (by
            unfold term_has_non_none_type at hNN
            simpa [__smtx_typeof] using hNN)
        rw [smtx_typeof_var_of_non_none s T hNN]
        exact smtx_type_fun_like_domains_no_reglan_of_type_wf hWf
    case UConst s T =>
        have hWf : __smtx_type_wf T = true :=
          Smtm.smtx_typeof_guard_wf_wf_of_non_none T T (by
            unfold term_has_non_none_type at hNN
            simpa [__smtx_typeof] using hNN)
        rw [smtx_typeof_uconst_of_non_none s T hNN]
        exact smtx_type_fun_like_domains_no_reglan_of_type_wf hWf
    case seq_empty T =>
        have hGuardNN : __smtx_typeof_guard_wf (SmtType.Seq T) (SmtType.Seq T) ≠ SmtType.None := by
          unfold term_has_non_none_type at hNN
          simpa [__smtx_typeof] using hNN
        have hSeqWf : __smtx_type_wf (SmtType.Seq T) = true :=
          Smtm.smtx_typeof_guard_wf_wf_of_non_none (SmtType.Seq T) (SmtType.Seq T) hGuardNN
        have hWf : __smtx_type_wf T = true :=
          Smtm.seq_type_wf_component_of_wf hSeqWf
        rw [smtx_typeof_seq_empty_of_non_none T hNN]
        change smtx_type_fun_like_domains_no_reglan T
        exact smtx_type_fun_like_domains_no_reglan_of_type_wf hWf
    case set_empty T =>
        have hGuardNN : __smtx_typeof_guard_wf (SmtType.Set T) (SmtType.Set T) ≠ SmtType.None := by
          unfold term_has_non_none_type at hNN
          simpa [__smtx_typeof] using hNN
        have hSetWf : __smtx_type_wf (SmtType.Set T) = true :=
          Smtm.smtx_typeof_guard_wf_wf_of_non_none (SmtType.Set T) (SmtType.Set T) hGuardNN
        have hWf : __smtx_type_wf T = true :=
          Smtm.set_type_wf_component_of_wf hSetWf
        rw [smtx_typeof_set_empty_of_non_none T hNN]
        change smtx_type_fun_like_domains_no_reglan T
        exact smtx_type_fun_like_domains_no_reglan_of_type_wf hWf
    case choice s T body =>
        exact choice_nth_fun_like_domains_no_reglan_any s T body hNN
    case bind s T x1 x2 =>
        have hTy : __smtx_typeof (SmtTerm.bind s T x1 x2) = __smtx_typeof x2 :=
          Smtm.bind_term_typeof_of_non_none hNN
        have hx2NN : term_has_non_none_type x2 := by
          unfold term_has_non_none_type at hNN ⊢
          rw [← hTy]; exact hNN
        rw [hTy]
        exact go x2 hx2NN
    case DtCons s d i =>
        exact smtx_typeof_dt_cons_no_reglan_of_non_none s d i hNN
    case ite c t1 t2 =>
        rcases ite_args_of_non_none hNN with ⟨T, hc, h1, h2, hT⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq_no_reglan h1 hT
        have hTy : __smtx_typeof (SmtTerm.ite c t1 t2) = T := by
          rw [typeof_ite_eq]
          simp [__smtx_typeof_ite, native_ite, native_Teq, hc, h1, h2]
        rw [hTy, ← h1]
        exact go t1 ht1
    case select t1 t2 =>
        rcases select_args_of_non_none hNN with ⟨A, B, h1, h2⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq_no_reglan h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.select t1 t2) = B := by
          rw [typeof_select_eq]
          simp [__smtx_typeof_select, native_ite, native_Teq, h1, h2]
        have hWFMap := go t1 ht1
        rw [hTy]
        rw [h1] at hWFMap
        exact hWFMap.2
    case store t1 t2 t3 =>
        rcases store_args_of_non_none hNN with ⟨A, B, h1, h2, h3⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq_no_reglan h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.store t1 t2 t3) = SmtType.Map A B := by
          rw [typeof_store_eq]
          simp [__smtx_typeof_store, native_ite, native_Teq, h1, h2, h3]
        have hWFMap := go t1 ht1
        rw [hTy]
        rw [h1] at hWFMap
        exact hWFMap
    case seq_unit t =>
        have hArgNN : term_has_non_none_type t := by
          unfold term_has_non_none_type at hNN ⊢
          rw [typeof_seq_unit_eq] at hNN
          by_cases hTy : __smtx_typeof t = SmtType.None
          · simp [__smtx_typeof_guard_wf, __smtx_type_wf, __smtx_type_wf_rec,
              native_and, native_ite, hTy] at hNN
          · exact hTy
        have hTy :
            __smtx_typeof (SmtTerm.seq_unit t) = SmtType.Seq (__smtx_typeof t) := by
          rw [typeof_seq_unit_eq]
          exact smtx_typeof_guard_wf_of_non_none (SmtType.Seq (__smtx_typeof t))
            (SmtType.Seq (__smtx_typeof t)) (by
              unfold term_has_non_none_type at hNN
              rw [typeof_seq_unit_eq] at hNN
              exact hNN)
        rw [hTy]
        exact go t hArgNN
    case set_singleton t =>
        have hArgNN : term_has_non_none_type t := by
          unfold term_has_non_none_type at hNN ⊢
          rw [typeof_set_singleton_eq] at hNN
          by_cases hTy : __smtx_typeof t = SmtType.None
          · simp [__smtx_typeof_guard_wf, __smtx_type_wf, __smtx_type_wf_rec,
              native_and, native_ite, hTy] at hNN
          · exact hTy
        have hTy :
            __smtx_typeof (SmtTerm.set_singleton t) = SmtType.Set (__smtx_typeof t) := by
          rw [typeof_set_singleton_eq]
          exact smtx_typeof_guard_wf_of_non_none (SmtType.Set (__smtx_typeof t))
            (SmtType.Set (__smtx_typeof t)) (by
              unfold term_has_non_none_type at hNN
              rw [typeof_set_singleton_eq] at hNN
              exact hNN)
        rw [hTy]
        exact go t hArgNN
    case seq_nth t1 t2 =>
        rcases seq_nth_args_of_non_none hNN with ⟨T, h1, h2⟩
        have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
          unfold term_has_non_none_type at hNN
          rw [typeof_seq_nth_eq, h1, h2] at hNN
          simpa [__smtx_typeof_seq_nth] using hNN
        have hTy : __smtx_typeof (SmtTerm.seq_nth t1 t2) = T := by
          rw [typeof_seq_nth_eq, h1, h2]
          simpa [__smtx_typeof_seq_nth] using
            smtx_typeof_guard_wf_of_non_none T T hGuardNN
        have hWF : __smtx_type_wf T = true :=
          Smtm.smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
        rw [hTy]
        exact smtx_type_fun_like_domains_no_reglan_of_type_wf hWF
    case str_rev t =>
        rcases seq_arg_of_non_none (op := SmtTerm.str_rev) (t := t)
            (typeof_str_rev_eq t) hNN with ⟨T, h1⟩
        have ht : term_has_non_none_type t :=
          smtx_term_has_non_none_of_type_eq_no_reglan h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.str_rev t) = SmtType.Seq T := by
          rw [typeof_str_rev_eq, h1]
          simp [__smtx_typeof_seq_op_1]
        rw [hTy]
        simpa [h1] using go t ht
    case str_concat t1 t2 =>
        rcases seq_binop_args_of_non_none (op := SmtTerm.str_concat)
            (typeof_str_concat_eq t1 t2) hNN with ⟨T, h1, h2⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq_no_reglan h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.str_concat t1 t2) = SmtType.Seq T := by
          rw [typeof_str_concat_eq, h1, h2]
          simp [__smtx_typeof_seq_op_2, native_ite, native_Teq]
        rw [hTy]
        simpa [h1] using go t1 ht1
    case str_substr t1 t2 t3 =>
        rcases str_substr_args_of_non_none hNN with ⟨T, h1, h2, h3⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq_no_reglan h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.str_substr t1 t2 t3) = SmtType.Seq T := by
          rw [typeof_str_substr_eq, h1, h2, h3]
          simp [__smtx_typeof_str_substr]
        rw [hTy]
        simpa [h1] using go t1 ht1
    case str_at t1 t2 =>
        rcases str_at_args_of_non_none hNN with ⟨T, h1, h2⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq_no_reglan h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.str_at t1 t2) = SmtType.Seq T := by
          rw [typeof_str_at_eq, h1, h2]
          simp [__smtx_typeof_str_at]
        rw [hTy]
        simpa [h1] using go t1 ht1
    case str_update t1 t2 t3 =>
        rcases str_update_args_of_non_none hNN with ⟨T, h1, h2, h3⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq_no_reglan h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.str_update t1 t2 t3) = SmtType.Seq T := by
          rw [typeof_str_update_eq, h1, h2, h3]
          simp [__smtx_typeof_str_update, native_ite, native_Teq]
        rw [hTy]
        simpa [h1] using go t1 ht1
    case str_replace t1 t2 t3 =>
        rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace)
            (typeof_str_replace_eq t1 t2 t3) hNN with ⟨T, h1, h2, h3⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq_no_reglan h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.str_replace t1 t2 t3) = SmtType.Seq T := by
          rw [typeof_str_replace_eq, h1, h2, h3]
          simp [__smtx_typeof_seq_op_3, native_ite, native_Teq]
        rw [hTy]
        simpa [h1] using go t1 ht1
    case str_replace_all t1 t2 t3 =>
        rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace_all)
            (typeof_str_replace_all_eq t1 t2 t3) hNN with ⟨T, h1, h2, h3⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq_no_reglan h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.str_replace_all t1 t2 t3) = SmtType.Seq T := by
          rw [typeof_str_replace_all_eq, h1, h2, h3]
          simp [__smtx_typeof_seq_op_3, native_ite, native_Teq]
        rw [hTy]
        simpa [h1] using go t1 ht1
    case set_union t1 t2 =>
        rcases set_binop_args_of_non_none (op := SmtTerm.set_union)
            (typeof_set_union_eq t1 t2) hNN with ⟨A, h1, h2⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq_no_reglan h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.set_union t1 t2) = SmtType.Set A := by
          rw [typeof_set_union_eq, h1, h2]
          simp [__smtx_typeof_sets_op_2, native_ite, native_Teq]
        rw [hTy]
        simpa [h1] using go t1 ht1
    case set_inter t1 t2 =>
        rcases set_binop_args_of_non_none (op := SmtTerm.set_inter)
            (typeof_set_inter_eq t1 t2) hNN with ⟨A, h1, h2⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq_no_reglan h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.set_inter t1 t2) = SmtType.Set A := by
          rw [typeof_set_inter_eq, h1, h2]
          simp [__smtx_typeof_sets_op_2, native_ite, native_Teq]
        rw [hTy]
        simpa [h1] using go t1 ht1
    case set_minus t1 t2 =>
        rcases set_binop_args_of_non_none (op := SmtTerm.set_minus)
            (typeof_set_minus_eq t1 t2) hNN with ⟨A, h1, h2⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq_no_reglan h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.set_minus t1 t2) = SmtType.Set A := by
          rw [typeof_set_minus_eq, h1, h2]
          simp [__smtx_typeof_sets_op_2, native_ite, native_Teq]
        rw [hTy]
        simpa [h1] using go t1 ht1
    case map_diff t1 t2 =>
        rcases map_diff_args_of_non_none hNN with hMap | hSet
        · rcases hMap with ⟨A, B, h1, h2, hTy⟩
          have ht1 : term_has_non_none_type t1 :=
            smtx_term_has_non_none_of_type_eq_no_reglan h1 (by simp)
          have hHead : smtx_type_fun_like_domains_no_reglan (SmtType.Map A B) := by
            simpa [h1] using go t1 ht1
          rw [hTy]
          exact hHead.1
        · rcases hSet with ⟨A, h1, h2, hTy⟩
          have ht1 : term_has_non_none_type t1 :=
            smtx_term_has_non_none_of_type_eq_no_reglan h1 (by simp)
          have hHead : smtx_type_fun_like_domains_no_reglan (SmtType.Set A) := by
            simpa [h1] using go t1 ht1
          rw [hTy]
          simpa [smtx_type_fun_like_domains_no_reglan] using hHead
    case _at_purify t1 =>
        have ht1 : term_has_non_none_type t1 := by
          intro hNone
          apply hNN
          simpa [__smtx_typeof] using hNone
        simpa [__smtx_typeof] using go t1 ht1
    case «exists» s T body =>
      have hBody : __smtx_typeof body = SmtType.Bool :=
        exists_body_bool_of_non_none hNN
      have hEq : native_Teq (__smtx_typeof body) SmtType.Bool = true := by
        simpa [native_Teq] using hBody
      have hGuardNN : __smtx_typeof_guard_wf T SmtType.Bool ≠ SmtType.None := by
        unfold term_has_non_none_type at hNN
        intro hNone
        apply hNN
        rw [typeof_exists_eq]
        simp [hEq, native_ite, hNone]
      have hGuard : __smtx_typeof_guard_wf T SmtType.Bool = SmtType.Bool :=
        smtx_typeof_guard_wf_of_non_none T SmtType.Bool hGuardNN
      rw [typeof_exists_eq]
      simp [hEq, native_ite, hGuard, smtx_type_fun_like_domains_no_reglan]
    case «forall» s T body =>
      have hBody : __smtx_typeof body = SmtType.Bool :=
        forall_body_bool_of_non_none hNN
      have hEq : native_Teq (__smtx_typeof body) SmtType.Bool = true := by
        simpa [native_Teq] using hBody
      have hGuardNN : __smtx_typeof_guard_wf T SmtType.Bool ≠ SmtType.None := by
        unfold term_has_non_none_type at hNN
        intro hNone
        apply hNN
        rw [typeof_forall_eq]
        simp [hEq, native_ite, hNone]
      have hGuard : __smtx_typeof_guard_wf T SmtType.Bool = SmtType.Bool :=
        smtx_typeof_guard_wf_of_non_none T SmtType.Bool hGuardNN
      rw [typeof_forall_eq]
      simp [hEq, native_ite, hGuard, smtx_type_fun_like_domains_no_reglan]
    all_goals
      simp only [__smtx_typeof, native_ite,
        __smtx_typeof_bv_op_1, __smtx_typeof_bv_op_1_ret,
        __smtx_typeof_bv_op_2, __smtx_typeof_bv_op_2_ret,
        __smtx_typeof_eq, __smtx_typeof_guard,
        __smtx_typeof_arith_overload_op_1, __smtx_typeof_arith_overload_op_2,
        __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_seq_op_1_ret,
        __smtx_typeof_seq_op_2_ret, __smtx_typeof_seq_diff, __smtx_typeof_str_indexof,
        __smtx_typeof_re_exp, __smtx_typeof_re_loop, __smtx_typeof_set_member,
        __smtx_typeof_sets_op_2_ret, __smtx_typeof_int_to_bv,
        __smtx_typeof_concat, __smtx_typeof_extract, __smtx_typeof_repeat,
        __smtx_typeof_zero_extend, __smtx_typeof_sign_extend,
        __smtx_typeof_rotate_left, __smtx_typeof_rotate_right]
      (repeat split) <;> try simp [smtx_type_fun_like_domains_no_reglan]
      all_goals
        split <;> simp [smtx_type_fun_like_domains_no_reglan]
  intro t hNN A B hHead
  exact smtx_type_fun_like_arg_ne_reglan_of_no_reglan (go t hNN) hHead
-/

private theorem eo_to_smt_type_eq_of_valid_rec_apply
    {refs : List native_String} {T U : Term}
    (hValid : eo_type_valid_rec refs T)
    (hEq : __eo_to_smt_type T = __eo_to_smt_type U) :
    T = U := by
  exact eo_to_smt_type_eq_of_valid_rec hValid hEq

private theorem eo_type_valid_of_valid_rec_top_apply
    {T : Term}
    (h : eo_type_valid_rec [] T) :
    eo_type_valid T := by
  simpa [eo_type_valid, eo_type_valid_rec] using h

private theorem eo_to_smt_typeof_matches_translation_apply_generic_from_valid_ih
    (f x : Term)
    (ihF :
      __smtx_typeof (__eo_to_smt f) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt f) = __eo_to_smt_type (__eo_typeof f) ∧
        eo_type_valid (__eo_typeof f))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) ∧
        eo_type_valid (__eo_typeof x))
    (hGeneric :
      generic_apply_type (__eo_to_smt f) (__eo_to_smt x))
    (hTranslate :
      __eo_to_smt (Term.Apply f x) =
        SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x))
    (hEoApply :
      __eo_typeof (Term.Apply f x) =
        __eo_typeof_apply (__eo_typeof f) (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply f x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply f x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply f x)) ∧
      eo_type_valid (__eo_typeof (Term.Apply f x)) := by
  have hApplyNN :
      __smtx_typeof_apply
          (__smtx_typeof (__eo_to_smt f)) (__smtx_typeof (__eo_to_smt x)) ≠
        SmtType.None := by
    have hApplyNN' :
        __smtx_typeof (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x)) ≠
          SmtType.None := by
      rw [← hTranslate]
      exact hNonNone
    rw [hGeneric] at hApplyNN'
    exact hApplyNN'
  rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, _hB⟩
  have hFNN : __smtx_typeof (__eo_to_smt f) ≠ SmtType.None := by
    exact smtx_head_non_none_of_apply_cases hHead
  have hXNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hX]
    exact hA
  have hFAll := ihF hFNN
  have hXAll := ihX hXNN
  have hXEo : __eo_to_smt_type (__eo_typeof x) = A := by
    simpa [hXAll.1] using hX
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply f x)) = B := by
    rw [hTranslate, hGeneric]
    exact smtx_typeof_apply_of_head_cases hHead hX hA
  cases hHead with
  | inl hFun =>
      have hFTrans :
          __eo_to_smt_type (__eo_typeof f) = SmtType.FunType A B := by
        rw [← hFAll.1]
        exact hFun
      rcases eo_to_smt_type_eq_fun hFTrans with
        ⟨T1, T2, hFunTy, hT1, hT2⟩
      have hFValid' : noNoneTy (SmtType.FunType A B) = true := by
        simpa [eo_type_valid, hFTrans] using hFAll.2
      have hParts : noNoneTy A = true ∧ noNoneTy B = true := by
        simpa [noNoneTy, native_and] using hFValid'
      rcases (by
        exact ⟨by simpa [eo_type_valid_rec, hT1] using hParts.1,
          by simpa [eo_type_valid_rec, hT2] using hParts.2⟩ :
          eo_type_valid_rec [] T1 ∧ eo_type_valid_rec [] T2) with
        ⟨hT1Valid, hT2Valid⟩
      have hArgTy : __eo_typeof x = T1 := by
        have hArgTy' : T1 = __eo_typeof x := by
          apply eo_to_smt_type_eq_of_valid_rec_apply hT1Valid
          rw [hT1, ← hXEo]
        exact hArgTy'.symm
      have hT1NotStuck : T1 ≠ Term.Stuck :=
        eo_type_valid_rec_not_stuck hT1Valid
      have hTypeApply :
          __eo_typeof_apply (Term.Apply (Term.Apply Term.FunType T1) T2) T1 = T2 := by
        rw [__eo_typeof_apply.eq_def]
        by_cases hStuck : T1 = Term.Stuck
        · exact False.elim (hT1NotStuck hStuck)
        · simp [hStuck, __eo_requires.eq_def, native_teq, native_ite, native_not]
      refine ⟨?_, ?_⟩
      · rw [hSmt, hEoApply, hFunTy, hArgTy, hTypeApply, hT2]
      · rw [hEoApply, hFunTy, hArgTy, hTypeApply]
        exact eo_type_valid_of_valid_rec_top_apply hT2Valid
  | inr hDtc =>
      have hFTrans :
          __eo_to_smt_type (__eo_typeof f) = SmtType.DtcAppType A B := by
        rw [← hFAll.1]
        exact hDtc
      rcases eo_to_smt_type_eq_dtc_app hFTrans with
        ⟨T1, T2, hDtcTy, hT1, hT2⟩
      have hFValid' : noNoneTy (SmtType.DtcAppType A B) = true := by
        simpa [eo_type_valid, hFTrans] using hFAll.2
      have hParts : noNoneTy A = true ∧ noNoneTy B = true := by
        simpa [noNoneTy, native_and] using hFValid'
      rcases (by
        exact ⟨by simpa [eo_type_valid_rec, hT1] using hParts.1,
          by simpa [eo_type_valid_rec, hT2] using hParts.2⟩ :
          eo_type_valid_rec [] T1 ∧ eo_type_valid_rec [] T2) with
        ⟨hT1Valid, hT2Valid⟩
      have hArgTy : __eo_typeof x = T1 := by
        have hArgTy' : T1 = __eo_typeof x := by
          apply eo_to_smt_type_eq_of_valid_rec_apply hT1Valid
          rw [hT1, ← hXEo]
        exact hArgTy'.symm
      have hT1NotStuck : T1 ≠ Term.Stuck :=
        eo_type_valid_rec_not_stuck hT1Valid
      have hTypeApply :
          __eo_typeof_apply (Term.DtcAppType T1 T2) T1 = T2 := by
        rw [__eo_typeof_apply.eq_def]
        by_cases hStuck : T1 = Term.Stuck
        · exact False.elim (hT1NotStuck hStuck)
        · simp [hStuck, __eo_requires.eq_def, native_teq, native_ite, native_not]
      refine ⟨?_, ?_⟩
      · rw [hSmt, hEoApply, hDtcTy, hArgTy, hTypeApply, hT2]
      · rw [hEoApply, hDtcTy, hArgTy, hTypeApply]
        exact eo_type_valid_of_valid_rec_top_apply hT2Valid

private theorem eo_to_smt_typeof_matches_translation_apply_generic_from_ih_of_valid
    (f x : Term)
    (ihF :
      __smtx_typeof (__eo_to_smt f) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt f) = __eo_to_smt_type (__eo_typeof f) ∧
        eo_type_valid (__eo_typeof f))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) ∧
        eo_type_valid (__eo_typeof x))
    (hGeneric :
      generic_apply_type (__eo_to_smt f) (__eo_to_smt x))
    (hTranslate :
      __eo_to_smt (Term.Apply f x) =
        SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x))
    (hEoApply :
      __eo_typeof (Term.Apply f x) =
        __eo_typeof_apply (__eo_typeof f) (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply f x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply f x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply f x)) := by
  exact
    (eo_to_smt_typeof_matches_translation_apply_generic_from_valid_ih
      f x ihF ihX
      hGeneric hTranslate hEoApply hNonNone).1

set_option maxHeartbeats 40000000 in
/-- Selector application typing, using the local IH for the selector argument. -/
private theorem eo_to_smt_type_typeof_apply_dt_sel_of_smt_datatype_from_ih
    (x : Term) (s : native_String) (d : DatatypeDecl) (i j : native_Nat)
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hReserved : __eo_reserved_datatype_name s = false)
    (hx : __smtx_typeof (__eo_to_smt x) =
      SmtType.Datatype s (__eo_to_smt_datatype_decl d))
    (hApplyNN :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.DtSel s (__eo_to_smt_datatype_decl d) i j)
          (__eo_to_smt x))) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.DtSel s d i j) x)) =
      __smtx_ret_typeof_sel s (__eo_to_smt_datatype_decl d) i j := by
  have hxNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hx]
    simp
  have hXTrans :
      __eo_to_smt_type (__eo_typeof x) =
        SmtType.Datatype s (__eo_to_smt_datatype_decl d) := by
    rw [← ihX hxNN]
    exact hx
  let dd := __eo_to_smt_datatype_decl d
  have hBaseWf : __smtx_type_wf (SmtType.Datatype s dd) = true :=
    Smtm.smt_datatype_wf_of_non_none_type (__eo_to_smt x) s dd (by simpa [dd] using hx)
  have hRecWf : __smtx_type_wf_rec (SmtType.Datatype s dd) = true :=
    smtx_type_wf_rec_of_type_wf (by simp) (by intro A B h; cases h)
      (by intro A B h; cases h) hBaseWf
  have hTypeNoNone : noNoneTy (SmtType.Datatype s dd) = true :=
    noNoneTy_of_wf _ hRecWf
  have hXValid : eo_type_valid_rec [] (__eo_typeof x) := by
    simpa [eo_type_valid_rec, hXTrans, dd] using hTypeNoNone
  have hxType : __eo_typeof x = Term.DatatypeType s d :=
    eo_to_smt_type_eq_of_valid_rec hXValid (by
      simpa [__eo_to_smt_type, hReserved, native_ite, dd] using hXTrans)
  have hLookupWf : __smtx_dt_wf_rec dd (__smtx_dd_lookup s dd) = true :=
    Smtm.datatype_wf_rec_of_type_wf hBaseWf
  have hLookupNoNone : noNoneDt (__smtx_dd_lookup s dd) = true :=
    noNoneDt_of_wf dd (__smtx_dd_lookup s dd) hLookupWf
  have hDeclNoNone : noNoneDecl dd = true := by
    simpa [noNoneTy] using hTypeNoNone
  have hEo :
      __eo_typeof (Term.Apply (Term.DtSel s d i j) x) =
        __eo_typeof_dt_sel_return (__eo_dd_resolve s d) i j := by
    change
      __eo_typeof_apply (__eo_typeof (Term.DtSel s d i j)) (__eo_typeof x) =
        __eo_typeof_dt_sel_return (__eo_dd_resolve s d) i j
    rw [hxType]
    simp [__eo_typeof, __eo_typeof_apply, __eo_requires,
      native_teq, native_ite, native_not]
  rw [hEo, eo_to_smt_typeof_dt_sel_return]
  unfold __smtx_ret_typeof_sel
  rw [eo_to_smt_dd_resolve_of_no_none s d
    (by simpa [dd] using hLookupNoNone)
    (by simpa [dd] using hDeclNoNone)]

private theorem eo_to_smt_typeof_matches_translation_apply_set_member_from_ih
    (x y : Term)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_member) y) x)) ≠
        SmtType.None) :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_member) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.set_member) y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_member) y) x) =
        SmtTerm.set_member (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hApplyNN :
      term_has_non_none_type (SmtTerm.set_member (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases set_member_args_of_non_none hApplyNN with ⟨A, hY, hX⟩
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_member) y) x)) =
        SmtType.Bool := by
    rw [hTranslate, typeof_set_member_eq (__eo_to_smt y) (__eo_to_smt x)]
    simp [__smtx_typeof_set_member, native_ite, native_Teq, hY, hX]
  have hAWF :
      smtx_type_field_wf_rec A native_reflist_nil :=
    smtx_set_component_field_wf_rec_of_non_none_type_apply (__eo_to_smt x) A hX
  have hANN : A ≠ SmtType.None :=
    smtx_type_field_wf_rec_ne_none hAWF
  rcases eo_typeof_eq_set_of_smt_set_from_ih x ihX hX with ⟨U, hXU, hU⟩
  have hYTrans : __eo_to_smt_type (__eo_typeof y) = A := by
    have hYNN : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
      rw [hY]
      exact hANN
    rw [← ihY hYNN]
    exact hY
  have hYU : __eo_typeof y = U :=
    eo_to_smt_type_injective_of_field_wf_rec hYTrans hU hAWF
  have hUNN : __eo_to_smt_type U ≠ SmtType.None := by
    rw [hU]
    exact hANN
  have hUNS : U ≠ Term.Stuck :=
    eo_term_ne_stuck_of_smt_type_non_none U hUNN
  have hEo :
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.set_member) y) x)) =
        SmtType.Bool := by
    change __eo_to_smt_type (__eo_typeof_set_member (__eo_typeof y) (__eo_typeof x)) =
      SmtType.Bool
    rw [hYU, hXU]
    simpa [__eo_typeof_set_member] using
      congrArg __eo_to_smt_type
        (eo_requires_eo_eq_self_of_non_stuck U Term.Bool hUNS)
  exact hSmt.trans hEo.symm

/--
Nested generic application once the translated head is known to be ordinary SMT
application. This version threads the explicit IH for the outer argument, while
the remaining validity obligation is still centralized in the local bridge.
-/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_generic_from_ih
    (g y x : Term)
    (ihHead :
      __smtx_typeof (__eo_to_smt (Term.Apply g y)) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt (Term.Apply g y)) =
        __eo_to_smt_type (__eo_typeof (Term.Apply g y)) ∧
        eo_type_valid (__eo_typeof (Term.Apply g y)))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) ∧
        eo_type_valid (__eo_typeof x))
    (hGeneric :
      generic_apply_type (__eo_to_smt (Term.Apply g y)) (__eo_to_smt x))
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply g y) x) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply g y)) (__eo_to_smt x))
    (hEoApply :
      __eo_typeof (Term.Apply (Term.Apply g y) x) =
        __eo_typeof_apply (__eo_typeof (Term.Apply g y)) (__eo_typeof x)) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply g y) x)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply g y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply g y) x)) := by
  intro hNonNone
  exact eo_to_smt_typeof_matches_translation_apply_generic_from_ih_of_valid
    (Term.Apply g y) x ihHead ihX hGeneric hTranslate hEoApply hNonNone

/--
Ternary nested generic application. This mirrors the older generic helper but
receives the final argument IH explicitly.
-/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_from_ih
    (g z y x : Term)
    (ihHead :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply g z) y)) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply g z) y)) =
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply g z) y)) ∧
        eo_type_valid (__eo_typeof (Term.Apply (Term.Apply g z) y)))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) ∧
        eo_type_valid (__eo_typeof x))
    (hGeneric :
      generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply g z) y)) (__eo_to_smt x))
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply g z) y) x) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply g z) y)) (__eo_to_smt x))
    (hEoApply :
      __eo_typeof (Term.Apply (Term.Apply (Term.Apply g z) y) x) =
        __eo_typeof_apply (__eo_typeof (Term.Apply (Term.Apply g z) y)) (__eo_typeof x)) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply g z) y) x)) ≠
      SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply g z) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply g z) y) x)) := by
  intro hNonNone
  exact eo_to_smt_typeof_matches_translation_apply_generic_from_ih_of_valid
    (Term.Apply (Term.Apply g z) y) x ihHead ihX hGeneric hTranslate hEoApply hNonNone

/-- Variant for exposed non-special heads shaped as `(UOp op) y`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_generic_of_head_from_ih
    (op : UserOp) (y x : Term) (head : SmtTerm)
    (ihHead :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp op) y)) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp op) y)) =
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp op) y)) ∧
        eo_type_valid (__eo_typeof (Term.Apply (Term.UOp op) y)))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) ∧
        eo_type_valid (__eo_typeof x))
    (hHeadTranslate :
      __eo_to_smt (Term.Apply (Term.UOp op) y) = head)
    (hOuterTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) y) x) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.UOp op) y)) (__eo_to_smt x))
    (hEoApply :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) y) x) =
        __eo_typeof_apply (__eo_typeof (Term.Apply (Term.UOp op) y)) (__eo_typeof x))
    (hSel : ∀ s d i j, head ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, head ≠ SmtTerm.DtTester s d i) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) y) x)) ≠
      SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp op) y) x)) := by
  intro hNonNone
  have hGeneric :
      generic_apply_type
        (__eo_to_smt (Term.Apply (Term.UOp op) y)) (__eo_to_smt x) := by
    simpa [hHeadTranslate] using
      (generic_apply_type_of_non_special_head head (__eo_to_smt x) hSel hTester)
  exact eo_to_smt_typeof_matches_translation_apply_apply_generic_from_ih
    (Term.UOp op) y x ihHead ihX hGeneric hOuterTranslate hEoApply hNonNone

private theorem noNoneTy_ne_none_apply
    {T : SmtType} (h : noNoneTy T = true) : T ≠ SmtType.None := by
  intro hNone
  subst T
  simp [noNoneTy] at h

private theorem eo_to_smt_typeof_dt_cons_rec_zero_of_no_none_apply :
    ∀ (T : Term) (c : DatatypeCons) (d : Datatype),
    T ≠ Term.Stuck →
    noNoneTy (__eo_to_smt_type T) = true →
    noNoneDt (__eo_to_smt_datatype (Datatype.sum c d)) = true →
    __eo_to_smt_type
        (__eo_typeof_dt_cons_rec T (Datatype.sum c d) native_nat_zero) =
      __smtx_typeof_dt_cons_rec (__eo_to_smt_type T)
        (__eo_to_smt_datatype (Datatype.sum c d)) native_nat_zero ∧
      noNoneTy
        (__smtx_typeof_dt_cons_rec (__eo_to_smt_type T)
          (__eo_to_smt_datatype (Datatype.sum c d)) native_nat_zero) = true := by
  intro T c d hTNS hT hD
  cases c with
  | unit =>
      simpa [__eo_typeof_dt_cons_rec, __smtx_typeof_dt_cons_rec,
        __eo_to_smt_datatype, __eo_to_smt_datatype_cons, hTNS] using hT
  | cons U c =>
      have hp :
          (noNoneTy (__eo_to_smt_type U) = true ∧
            noNoneDtc (__eo_to_smt_datatype_cons c) = true) ∧
              noNoneDt (__eo_to_smt_datatype d) = true := by
        simpa [__eo_to_smt_datatype, __eo_to_smt_datatype_cons,
          noNoneDt, noNoneDtc, native_and] using hD
      have hTail :
          noNoneDt
            (__eo_to_smt_datatype (Datatype.sum c d)) = true := by
        simp [__eo_to_smt_datatype, noNoneDt, native_and, hp.1.2, hp.2]
      have hRec := eo_to_smt_typeof_dt_cons_rec_zero_of_no_none_apply
        T c d hTNS hT hTail
      have hUNN : __eo_to_smt_type U ≠ SmtType.None :=
        noNoneTy_ne_none_apply hp.1.1
      have hRecNN :
          __smtx_typeof_dt_cons_rec (__eo_to_smt_type T)
              (__eo_to_smt_datatype (Datatype.sum c d)) 0 ≠ SmtType.None :=
        noNoneTy_ne_none_apply hRec.2
      have hRecNN' :
          __smtx_typeof_dt_cons_rec (__eo_to_smt_type T)
              (SmtDatatype.sum (__eo_to_smt_datatype_cons c)
                (__eo_to_smt_datatype d)) 0 ≠ SmtType.None := by
        simpa [__eo_to_smt_datatype] using hRecNN
      constructor
      · simp [__eo_typeof_dt_cons_rec, __smtx_typeof_dt_cons_rec,
          __eo_to_smt_datatype, __eo_to_smt_datatype_cons,
          hRec.1, hUNN, hRecNN', __smtx_typeof_guard, native_ite, native_Teq]
      · simpa [__smtx_typeof_dt_cons_rec, __eo_to_smt_datatype,
          __eo_to_smt_datatype_cons, noNoneTy, native_and] using
          And.intro hp.1.1 hRec.2

private theorem eo_to_smt_typeof_dt_cons_rec_of_no_none_apply
    (T : Term) :
    ∀ (d : Datatype) (i : native_Nat),
      T ≠ Term.Stuck ->
      noNoneTy (__eo_to_smt_type T) = true ->
      noNoneDt (__eo_to_smt_datatype d) = true ->
      __eo_to_smt_type (__eo_typeof_dt_cons_rec T d i) =
        __smtx_typeof_dt_cons_rec (__eo_to_smt_type T)
          (__eo_to_smt_datatype d) i ∧
      (__smtx_typeof_dt_cons_rec (__eo_to_smt_type T)
          (__eo_to_smt_datatype d) i ≠ SmtType.None ->
        noNoneTy
          (__smtx_typeof_dt_cons_rec (__eo_to_smt_type T)
            (__eo_to_smt_datatype d) i) = true)
  | Datatype.null, i, hTNS, hT, hD => by
      cases i <;> simp [__eo_typeof_dt_cons_rec, __smtx_typeof_dt_cons_rec,
        __eo_to_smt_datatype, __eo_to_smt_type]
  | Datatype.sum c d, native_nat_zero, hTNS, hT, hD => by
      have hz := eo_to_smt_typeof_dt_cons_rec_zero_of_no_none_apply
        T c d hTNS hT hD
      exact ⟨hz.1, fun _ => hz.2⟩
  | Datatype.sum c d, native_nat_succ i, hTNS, hT, hD => by
      have hp :
          noNoneDtc (__eo_to_smt_datatype_cons c) = true ∧
            noNoneDt (__eo_to_smt_datatype d) = true := by
        simpa [__eo_to_smt_datatype, noNoneDt, native_and] using hD
      simpa [__eo_typeof_dt_cons_rec, __smtx_typeof_dt_cons_rec,
        __eo_to_smt_datatype, hTNS] using
        eo_to_smt_typeof_dt_cons_rec_of_no_none_apply T d i hTNS hT hp.2

theorem eo_to_smt_type_typeof_dt_cons_decl_of_non_none
    (s : native_String) (d : DatatypeDecl) (i : native_Nat)
    (hReserved : __eo_reserved_datatype_name s = false)
    (hNN :
      __smtx_typeof (SmtTerm.DtCons s (__eo_to_smt_datatype_decl d) i) ≠
        SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.DtCons s d i)) =
        __smtx_typeof (SmtTerm.DtCons s (__eo_to_smt_datatype_decl d) i) ∧
      eo_type_valid_rec [] (__eo_typeof (Term.DtCons s d i)) := by
  let dd := __eo_to_smt_datatype_decl d
  let body := __smtx_dt_resolve (__smtx_dd_lookup s dd) dd
  let D : SmtType := SmtType.Datatype s dd
  let raw : SmtType := __smtx_typeof_dt_cons_rec D body i
  have hGuardNN : __smtx_typeof_guard_wf D raw ≠ SmtType.None := by
    simpa [D, raw, Smtm.typeof_dt_cons_eq] using hNN
  have hBaseTypeWf : __smtx_type_wf D = true :=
    Smtm.smtx_typeof_guard_wf_wf_of_non_none D raw hGuardNN
  have hLookupWf : __smtx_dt_wf_rec dd (__smtx_dd_lookup s dd) = true :=
    datatype_wf_rec_of_type_wf hBaseTypeWf
  have hLookupNoNone : noNoneDt (__smtx_dd_lookup s dd) = true :=
    noNoneDt_of_wf dd (__smtx_dd_lookup s dd) hLookupWf
  have hRecWf : __smtx_type_wf_rec D = true :=
    smtx_type_wf_rec_of_type_wf (by simp [D])
      (by intro X Y h; simp [D] at h)
      (by intro X Y h; simp [D] at h) hBaseTypeWf
  have hTypeNoNone : noNoneTy D = true := noNoneTy_of_wf D hRecWf
  have hDeclNoNone : noNoneDecl dd = true := by
    simpa [D, noNoneTy] using hTypeNoNone
  have hBodyNoNone : noNoneDt body = true :=
    noNoneDt_resolve (__smtx_dd_lookup s dd) dd hLookupNoNone hDeclNoNone
  have hResolve :
      __eo_to_smt_datatype (__eo_dd_resolve s d) = body :=
    eo_to_smt_dd_resolve_of_no_none s d
      (by simpa [dd] using hLookupNoNone)
      (by simpa [dd] using hDeclNoNone)
  have hEoBodyNoNone :
      noNoneDt (__eo_to_smt_datatype (__eo_dd_resolve s d)) = true := by
    rw [hResolve]
    exact hBodyNoNone
  have hBaseEoNoNone :
      noNoneTy (__eo_to_smt_type (Term.DatatypeType s d)) = true := by
    simpa [D, dd, __eo_to_smt_type, hReserved, native_ite] using hTypeNoNone
  have hRec := eo_to_smt_typeof_dt_cons_rec_of_no_none_apply
    (Term.DatatypeType s d) (__eo_dd_resolve s d) i
    (by simp) hBaseEoNoNone hEoBodyNoNone
  have hGuardEq : __smtx_typeof (SmtTerm.DtCons s dd i) = raw := by
    have hg := smtx_typeof_guard_wf_of_non_none D raw hGuardNN
    simpa [D, raw, body, Smtm.typeof_dt_cons_eq] using hg
  have hEoHeadEq :
      __eo_to_smt_type (__eo_typeof (Term.DtCons s d i)) = raw := by
    change __eo_to_smt_type
        (__eo_typeof_dt_cons_rec (Term.DatatypeType s d) (__eo_dd_resolve s d) i) = raw
    simpa [D, raw, dd, body, __eo_to_smt_type, hReserved, native_ite,
      hResolve] using hRec.1
  have hRawNN : raw ≠ SmtType.None := by
    rw [← hGuardEq]
    simpa [dd] using hNN
  have hRecRawNN :
      __smtx_typeof_dt_cons_rec
          (__eo_to_smt_type (Term.DatatypeType s d))
          (__eo_to_smt_datatype (__eo_dd_resolve s d)) i ≠ SmtType.None := by
    simpa [D, raw, dd, body, __eo_to_smt_type, hReserved, native_ite,
      hResolve] using hRawNN
  refine ⟨hEoHeadEq.trans hGuardEq.symm, ?_⟩
  unfold eo_type_valid_rec
  rw [hEoHeadEq]
  have hn := hRec.2 hRecRawNN
  simpa [D, raw, dd, body, __eo_to_smt_type, hReserved, native_ite,
    hResolve] using hn

private theorem eo_to_smt_type_typeof_apply_dt_cons_of_fun_like
    (x U V : Term) (s : native_String) (d : DatatypeDecl) (i : native_Nat)
    (hHead :
      __eo_typeof (Term.DtCons s d i) =
          Term.Apply (Term.Apply Term.FunType U) V ∨
        __eo_typeof (Term.DtCons s d i) = Term.DtcAppType U V)
    (hx : __eo_typeof x = U)
    (hUNN : __eo_to_smt_type U ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.DtCons s d i) x)) =
      __eo_to_smt_type V := by
  have hUNS : U ≠ Term.Stuck :=
    eo_term_ne_stuck_of_smt_type_non_none U hUNN
  cases hHead with
  | inl hFun =>
      change __eo_to_smt_type
          (__eo_typeof_apply (__eo_typeof (Term.DtCons s d i)) (__eo_typeof x)) =
        __eo_to_smt_type V
      rw [hFun, hx]
      simp [__eo_typeof_apply, __eo_requires, native_teq, native_ite,
        native_not, hUNS]
  | inr hDtc =>
      change __eo_to_smt_type
          (__eo_typeof_apply (__eo_typeof (Term.DtCons s d i)) (__eo_typeof x)) =
        __eo_to_smt_type V
      rw [hDtc, hx]
      simp [__eo_typeof_apply, __eo_requires, native_teq, native_ite,
        native_not, hUNS]

private theorem eo_to_smt_type_typeof_apply_dt_cons_of_smt_apply_from_ih
    (x : Term) (s : native_String) (d : DatatypeDecl) (i : native_Nat) (A B : SmtType)
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hReserved : __eo_reserved_datatype_name s = false)
    (hHead :
      __smtx_typeof (SmtTerm.DtCons s (__eo_to_smt_datatype_decl d) i) =
          SmtType.FunType A B ∨
        __smtx_typeof (SmtTerm.DtCons s (__eo_to_smt_datatype_decl d) i) =
          SmtType.DtcAppType A B)
    (hx : __smtx_typeof (__eo_to_smt x) = A)
    (hA : A ≠ SmtType.None)
    (hB : B ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.DtCons s d i) x)) = B := by
  have hHeadNN :
      __smtx_typeof (SmtTerm.DtCons s (__eo_to_smt_datatype_decl d) i) ≠
        SmtType.None := by
    cases hHead with
    | inl hFun =>
        rw [hFun]
        simp
    | inr hDtc =>
        rw [hDtc]
        simp
  let dd := __eo_to_smt_datatype_decl d
  let body := __smtx_dt_resolve (__smtx_dd_lookup s dd) dd
  let D : SmtType := SmtType.Datatype s dd
  let raw : SmtType :=
    __smtx_typeof_dt_cons_rec D body i
  have hGuardNN : __smtx_typeof_guard_wf D raw ≠ SmtType.None := by
    simpa [D, raw, Smtm.typeof_dt_cons_eq] using hHeadNN
  have hBaseTypeWf : __smtx_type_wf D = true :=
    Smtm.smtx_typeof_guard_wf_wf_of_non_none D raw hGuardNN
  have hLookupWf : __smtx_dt_wf_rec dd (__smtx_dd_lookup s dd) = true :=
    datatype_wf_rec_of_type_wf hBaseTypeWf
  have hLookupNoNone : noNoneDt (__smtx_dd_lookup s dd) = true :=
    noNoneDt_of_wf dd (__smtx_dd_lookup s dd) hLookupWf
  have hRecWf : __smtx_type_wf_rec D = true :=
    smtx_type_wf_rec_of_type_wf (by simp [D])
      (by intro X Y h; simp [D] at h) (by intro X Y h; simp [D] at h) hBaseTypeWf
  have hTypeNoNone : noNoneTy D = true := noNoneTy_of_wf D hRecWf
  have hDeclNoNone : noNoneDecl dd = true := by
    simpa [D, noNoneTy] using hTypeNoNone
  have hBodyNoNone : noNoneDt body = true := by
    exact noNoneDt_resolve (__smtx_dd_lookup s dd) dd hLookupNoNone hDeclNoNone
  have hResolve :
      __eo_to_smt_datatype (__eo_dd_resolve s d) = body := by
    exact eo_to_smt_dd_resolve_of_no_none s d
      (by simpa [dd] using hLookupNoNone)
      (by simpa [dd] using hDeclNoNone)
  have hEoBodyNoNone :
      noNoneDt (__eo_to_smt_datatype (__eo_dd_resolve s d)) = true := by
    rw [hResolve]
    exact hBodyNoNone
  have hBaseEoNoNone :
      noNoneTy (__eo_to_smt_type (Term.DatatypeType s d)) = true := by
    simpa [D, dd, __eo_to_smt_type, hReserved, native_ite] using hTypeNoNone
  have hRec := eo_to_smt_typeof_dt_cons_rec_of_no_none_apply
    (Term.DatatypeType s d) (__eo_dd_resolve s d) i
    (by simp) hBaseEoNoNone hEoBodyNoNone
  have hGuardEq : __smtx_typeof (SmtTerm.DtCons s dd i) = raw := by
    have hg := smtx_typeof_guard_wf_of_non_none D raw hGuardNN
    simpa [D, raw, body, Smtm.typeof_dt_cons_eq] using hg
  have hEoHeadEq :
      __eo_to_smt_type (__eo_typeof (Term.DtCons s d i)) = raw := by
    change __eo_to_smt_type
        (__eo_typeof_dt_cons_rec (Term.DatatypeType s d) (__eo_dd_resolve s d) i) = raw
    simpa [D, raw, dd, body, __eo_to_smt_type, hReserved, native_ite,
      hResolve] using hRec.1
  have hRawNN : raw ≠ SmtType.None := by
    rw [← hGuardEq]
    exact hHeadNN
  have hRecRawNN :
      __smtx_typeof_dt_cons_rec
          (__eo_to_smt_type (Term.DatatypeType s d))
          (__eo_to_smt_datatype (__eo_dd_resolve s d)) i ≠ SmtType.None := by
    simpa [D, raw, dd, body, __eo_to_smt_type, hReserved, native_ite,
      hResolve] using hRawNN
  have hHeadAll :
      __eo_to_smt_type (__eo_typeof (Term.DtCons s d i)) =
          __smtx_typeof (SmtTerm.DtCons s dd i) ∧
        eo_type_valid_rec [] (__eo_typeof (Term.DtCons s d i)) := by
    refine ⟨hEoHeadEq.trans hGuardEq.symm, ?_⟩
    unfold eo_type_valid_rec
    rw [hEoHeadEq]
    have hn := hRec.2 hRecRawNN
    simpa [D, raw, dd, body, __eo_to_smt_type, hReserved, native_ite,
      hResolve] using hn
  have hxNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hx]
    exact hA
  have hxEo : __eo_to_smt_type (__eo_typeof x) = A := by
    rw [← ihX hxNN]
    exact hx
  cases hHead with
  | inl hFun =>
      have hEoHead :
          __eo_to_smt_type (__eo_typeof (Term.DtCons s d i)) =
            SmtType.FunType A B := by
        exact hHeadAll.1.trans hFun
      rcases eo_to_smt_type_eq_fun hEoHead with
        ⟨U, V, hHeadEo, hU, hV⟩
      have hHeadValid : noNoneTy (SmtType.FunType A B) = true := by
        simpa [eo_type_valid_rec, hEoHead] using hHeadAll.2
      have hParts : noNoneTy A = true ∧ noNoneTy B = true := by
        simpa [noNoneTy, native_and] using hHeadValid
      rcases (by
        exact ⟨by simpa [eo_type_valid_rec, hU] using hParts.1,
          by simpa [eo_type_valid_rec, hV] using hParts.2⟩ :
          eo_type_valid_rec [] U ∧ eo_type_valid_rec [] V) with
        ⟨hUValid, _hVValid⟩
      have hxU : __eo_typeof x = U := by
        have hUx : U = __eo_typeof x := by
          apply eo_to_smt_type_eq_of_valid_rec hUValid
          rw [hU, ← hxEo]
        exact hUx.symm
      have hUNN : __eo_to_smt_type U ≠ SmtType.None := by
        rw [hU]
        exact hA
      have hApply :=
        eo_to_smt_type_typeof_apply_dt_cons_of_fun_like
          x U V s d i (Or.inl hHeadEo) hxU hUNN
      exact hApply.trans hV
  | inr hDtc =>
      have hEoHead :
          __eo_to_smt_type (__eo_typeof (Term.DtCons s d i)) =
            SmtType.DtcAppType A B := by
        exact hHeadAll.1.trans hDtc
      rcases eo_to_smt_type_eq_dtc_app hEoHead with
        ⟨U, V, hHeadEo, hU, hV⟩
      have hHeadValid : noNoneTy (SmtType.DtcAppType A B) = true := by
        simpa [eo_type_valid_rec, hEoHead] using hHeadAll.2
      have hParts : noNoneTy A = true ∧ noNoneTy B = true := by
        simpa [noNoneTy, native_and] using hHeadValid
      rcases (by
        exact ⟨by simpa [eo_type_valid_rec, hU] using hParts.1,
          by simpa [eo_type_valid_rec, hV] using hParts.2⟩ :
          eo_type_valid_rec [] U ∧ eo_type_valid_rec [] V) with
        ⟨hUValid, _hVValid⟩
      have hxU : __eo_typeof x = U := by
        have hUx : U = __eo_typeof x := by
          apply eo_to_smt_type_eq_of_valid_rec hUValid
          rw [hU, ← hxEo]
        exact hUx.symm
      have hUNN : __eo_to_smt_type U ≠ SmtType.None := by
        rw [hU]
        exact hA
      have hApply :=
        eo_to_smt_type_typeof_apply_dt_cons_of_fun_like
          x U V s d i (Or.inr hHeadEo) hxU hUNN
      exact hApply.trans hV

/-- Computes the type of a non-`None` `re_exp` term. -/
private theorem re_exp_typeof_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.re_exp t1 t2)) :
    __smtx_typeof (SmtTerm.re_exp t1 t2) = SmtType.RegLan := by
  rw [typeof_re_exp_eq]
  unfold term_has_non_none_type at ht
  rw [typeof_re_exp_eq] at ht
  cases t1 <;> simp [__smtx_typeof_re_exp] at ht ⊢
  case Numeral n =>
    cases h2 : __smtx_typeof t2 <;> simp [h2] at ht ⊢
    by_cases hn : native_zleq 0 n <;> simp [hn, native_ite] at ht ⊢

/-- Extracts the argument types of a non-`None` `re_exp` term. -/
private theorem re_exp_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.re_exp t1 t2)) :
    (∃ n : native_Int, t1 = SmtTerm.Numeral n ∧ native_zleq 0 n = true) ∧
      __smtx_typeof t2 = SmtType.RegLan := by
  unfold term_has_non_none_type at ht
  rw [typeof_re_exp_eq] at ht
  cases t1 <;> simp [__smtx_typeof_re_exp] at ht
  case Numeral n =>
    cases h2 : __smtx_typeof t2 <;> simp [h2] at ht
    by_cases hn : native_zleq 0 n = true
    · exact ⟨⟨n, rfl, hn⟩, rfl⟩
    · exfalso
      cases hz : native_zleq 0 n <;> simp [hz] at hn ht
      exact ht rfl

/-- Simplifies EO-to-SMT translation for `re_exp`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_re_exp
    (x y : Term)
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.re_exp y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.re_exp y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.re_exp y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.UOp1 UserOp1.re_exp y) x) =
        SmtTerm.re_exp (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hApplyNN :
      term_has_non_none_type (SmtTerm.re_exp (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.re_exp y) x)) =
        SmtType.RegLan := by
    rw [hTranslate]
    exact re_exp_typeof_of_non_none hApplyNN
  rcases re_exp_args_of_non_none hApplyNN with ⟨⟨n, hYNum, hn⟩, hXRegLan⟩
  have hYInt : __smtx_typeof (__eo_to_smt y) = SmtType.Int := by
    rw [hYNum]
    unfold __smtx_typeof
    rfl
  have hYTerm : y = Term.Numeral n :=
    eo_to_smt_eq_numeral y n hYNum
  have hYEo : __eo_typeof y = Term.UOp UserOp.Int := by
    rw [hYTerm]
    rfl
  have hXEo : __eo_typeof x = Term.UOp UserOp.RegLan :=
    eo_typeof_eq_reglan_of_smt_reglan_from_ih x ihX hXRegLan
  have hEo :
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.re_exp y) x)) =
        SmtType.RegLan := by
    change __eo_to_smt_type (__eo_typeof_re_exp (__eo_typeof y) y (__eo_typeof x)) =
      SmtType.RegLan
    have hnGt : native_zlt (-1 : native_Int) n = true :=
      native_zlt_neg_one_of_zleq_zero hn
    rw [hYTerm, hXEo]
    change
      __eo_to_smt_type
          (__eo_typeof_re_exp (Term.UOp UserOp.Int) (Term.Numeral n)
            (Term.UOp UserOp.RegLan)) =
        SmtType.RegLan
    simp [__eo_typeof_re_exp, __eo_gt, __eo_requires, native_teq, native_not,
      native_ite, hnGt]
  exact hSmt.trans hEo.symm

/-- Proof for the opaque `_at_strings_stoi_result` application. -/
private theorem eo_to_smt_typeof_matches_translation_apply_at_strings_stoi_result
    (x y : Term)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term._at_strings_stoi_result y) x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term._at_strings_stoi_result y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term._at_strings_stoi_result y) x)) := by
  let zero := SmtTerm.Numeral 0
  let prefixTerm := SmtTerm.str_substr (__eo_to_smt y) zero (__eo_to_smt x)
  let parsed := SmtTerm.str_to_int prefixTerm
  let rhs := SmtTerm.ite (SmtTerm.eq (__eo_to_smt x) zero) zero parsed
  have hTranslate :
      __eo_to_smt (Term.Apply (Term._at_strings_stoi_result y) x) =
        rhs := by
    rfl
  have hApplyNN : term_has_non_none_type rhs := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases ite_args_of_non_none hApplyNN with
    ⟨T, hCond, hZero, hParsed, hTNonNone⟩
  have hZeroInt : __smtx_typeof zero = SmtType.Int := by
    rfl
  have hTInt : T = SmtType.Int := hZero.symm.trans hZeroInt
  have hSmt :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term._at_strings_stoi_result y) x)) =
        SmtType.Int := by
    rw [hTranslate, typeof_ite_eq, hCond, hZero, hParsed]
    simp [__smtx_typeof_ite, native_ite, native_Teq, hTInt]
  have hParsedNN : term_has_non_none_type parsed := by
    unfold term_has_non_none_type
    rw [hParsed, hTInt]
    simp
  have hPrefixSeqChar :
      __smtx_typeof prefixTerm = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := SmtTerm.str_to_int)
      (typeof_str_to_int_eq prefixTerm) hParsedNN
  have hPrefixNN : term_has_non_none_type prefixTerm := by
    unfold term_has_non_none_type
    rw [hPrefixSeqChar]
    simp
  rcases str_substr_args_of_non_none hPrefixNN with
    ⟨U, hYSeq, hStart, hXInt⟩
  have hPrefixSeqU : __smtx_typeof prefixTerm = SmtType.Seq U := by
    rw [show prefixTerm =
        SmtTerm.str_substr (__eo_to_smt y) zero (__eo_to_smt x) by rfl]
    rw [typeof_str_substr_eq (__eo_to_smt y) zero (__eo_to_smt x),
      hYSeq, hStart, hXInt]
    simp [__smtx_typeof_str_substr]
  have hUChar : U = SmtType.Char := by
    have hSeqEq : SmtType.Seq U = SmtType.Seq SmtType.Char :=
      hPrefixSeqU.symm.trans hPrefixSeqChar
    cases hSeqEq
    rfl
  subst U
  have hYEo :
      __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) :=
    eo_typeof_eq_seq_char_of_smt_seq_char_from_ih y ihY hYSeq
  have hXEo : __eo_typeof x = Term.UOp UserOp.Int :=
    eo_typeof_eq_int_of_smt_int_from_ih x ihX hXInt
  exact hSmt.trans
    (eo_to_smt_type_typeof_apply_apply_at_strings_stoi_result_of_seq_char_int
      x y hYEo hXEo).symm

/-- Simplifies EO-to-SMT translation for `_at_strings_itos_result`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_at_strings_itos_result
    (x y : Term)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term._at_strings_itos_result y) x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term._at_strings_itos_result y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term._at_strings_itos_result y) x)) := by
  let zero := SmtTerm.Numeral 0
  let fromInt := SmtTerm.str_from_int (__eo_to_smt y)
  let prefixTerm := SmtTerm.str_substr fromInt zero (__eo_to_smt x)
  let parsed := SmtTerm.str_to_int prefixTerm
  let rhs := SmtTerm.ite (SmtTerm.eq (__eo_to_smt x) zero) zero parsed
  have hTranslate :
      __eo_to_smt (Term.Apply (Term._at_strings_itos_result y) x) =
        rhs := by
    rfl
  have hApplyNN : term_has_non_none_type rhs := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases ite_args_of_non_none hApplyNN with
    ⟨T, hCond, hZero, hParsed, hTNonNone⟩
  have hZeroInt : __smtx_typeof zero = SmtType.Int := by
    rfl
  have hTInt : T = SmtType.Int := hZero.symm.trans hZeroInt
  have hSmt :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term._at_strings_itos_result y) x)) =
        SmtType.Int := by
    rw [hTranslate, typeof_ite_eq, hCond, hZero, hParsed]
    simp [__smtx_typeof_ite, native_ite, native_Teq, hTInt]
  have hParsedNN : term_has_non_none_type parsed := by
    unfold term_has_non_none_type
    rw [hParsed, hTInt]
    simp
  have hPrefixSeqChar : __smtx_typeof prefixTerm = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := SmtTerm.str_to_int)
      (typeof_str_to_int_eq prefixTerm) hParsedNN
  have hPrefixNN : term_has_non_none_type prefixTerm := by
    unfold term_has_non_none_type
    rw [hPrefixSeqChar]
    simp
  rcases str_substr_args_of_non_none hPrefixNN with
    ⟨U, hFromIntSeq, hStartInt, hXInt⟩
  have hPrefixSeqU : __smtx_typeof prefixTerm = SmtType.Seq U := by
    rw [show prefixTerm = SmtTerm.str_substr fromInt zero (__eo_to_smt x) by rfl]
    rw [typeof_str_substr_eq fromInt zero (__eo_to_smt x),
      hFromIntSeq, hStartInt, hXInt]
    simp [__smtx_typeof_str_substr]
  have hUChar : U = SmtType.Char := by
    have hSeqEq : SmtType.Seq U = SmtType.Seq SmtType.Char :=
      hPrefixSeqU.symm.trans hPrefixSeqChar
    cases hSeqEq
    rfl
  subst U
  have hFromIntNN : term_has_non_none_type fromInt := by
    unfold term_has_non_none_type
    rw [hFromIntSeq]
    simp
  have hYInt : __smtx_typeof (__eo_to_smt y) = SmtType.Int :=
    int_arg_of_non_none_ret (op := SmtTerm.str_from_int)
      (ret := SmtType.Seq SmtType.Char)
      (typeof_str_from_int_eq (__eo_to_smt y)) hFromIntNN
  have hYEo : __eo_typeof y = Term.UOp UserOp.Int :=
    eo_typeof_eq_int_of_smt_int_from_ih y ihY hYInt
  have hXEo : __eo_typeof x = Term.UOp UserOp.Int :=
    eo_typeof_eq_int_of_smt_int_from_ih x ihX hXInt
  have hEo :
      __eo_to_smt_type
          (__eo_typeof (Term.Apply (Term._at_strings_itos_result y) x)) =
        SmtType.Int := by
    change __eo_to_smt_type (__eo_typeof_div (__eo_typeof y) (__eo_typeof x)) = SmtType.Int
    rw [hYEo, hXEo]
    rfl
  exact hSmt.trans hEo.symm

/-- Applying an `_at_bv` translation as a function is ill-typed. -/
theorem typeof_apply_eo_to_smt_at_bv_eq_none
    (a b x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.int_to_bv b a) x) = SmtType.None := by
  exact typeof_generic_apply_non_function_head_eq_none _ _
    (generic_apply_type_of_non_special_head _ _
      (eo_to_smt_at_bv_ne_dt_sel a b)
      (eo_to_smt_at_bv_ne_dt_tester a b))
    (by
      intro A B hFun
      have hNN : __smtx_typeof (SmtTerm.int_to_bv b a) ≠ SmtType.None := by
        rw [hFun]
        simp
      rcases eo_to_smt_at_bv_of_non_none hNN with ⟨w, _hb, _ha, _hw, hTy⟩
      rw [hTy] at hFun
      cases hFun)
    (by
      intro A B hIFun
      have hNN : __smtx_typeof (SmtTerm.int_to_bv b a) ≠ SmtType.None := by
        rw [hIFun]
        simp
      rcases eo_to_smt_at_bv_of_non_none hNN with ⟨w, _hb, _ha, _hw, hTy⟩
      rw [hTy] at hIFun
      cases hIFun)
    (by
      intro A B hDtc
      have hNN : __smtx_typeof (SmtTerm.int_to_bv b a) ≠ SmtType.None := by
        rw [hDtc]
        simp
      rcases eo_to_smt_at_bv_of_non_none hNN with ⟨w, _hb, _ha, _hw, hTy⟩
      rw [hTy] at hDtc
      cases hDtc)

private theorem apply_eo_to_smt_type_bitvec_nat
    (w : native_Nat) :
    __eo_to_smt_type
        (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w))) =
      SmtType.BitVec w := by
  simp [__eo_to_smt_type, native_ite, native_zleq, SmtEval.native_zleq,
    native_nat_to_int, native_int_to_nat, Smtm.native_nat_to_int,
    SmtEval.native_int_to_nat]

private theorem apply_eo_to_smt_type_bitvec_int_of_nonneg
    (w : native_Int)
    (hw : native_zleq 0 w = true) :
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w)) =
      SmtType.BitVec (native_int_to_nat w) := by
  simp [__eo_to_smt_type, native_ite, hw]

private theorem native_zleq_zero_zmult_nat_of_one_le
    (i : native_Int) (w : native_Nat)
    (hi : native_zleq 1 i = true) :
    native_zleq 0 (native_zmult i (native_nat_to_int w)) = true := by
  have hiProp : (1 : Int) ≤ i := by
    simpa [native_zleq] using hi
  have hiNonneg : (0 : Int) ≤ i := Int.le_trans (by decide) hiProp
  have hwNonneg : (0 : Int) ≤ native_nat_to_int w := by
    unfold native_nat_to_int
    exact Int.natCast_nonneg w
  have hNonneg : (0 : Int) ≤ native_zmult i (native_nat_to_int w) := by
    unfold native_zmult
    exact Int.mul_nonneg hiNonneg hwNonneg
  simpa [native_zleq] using hNonneg

private theorem native_zleq_of_zlt_true
    (a b : native_Int)
    (h : native_zlt a b = true) :
    native_zleq a b = true := by
  unfold native_zlt at h
  unfold native_zleq
  by_cases hlt : a < b
  · have hle : a ≤ b := Int.le_of_lt hlt
    simp [hle]
  · simp [hlt] at h

private theorem native_zleq_zero_zplus_nat_right_of_nonneg
    (i : native_Int) (w : native_Nat)
    (hi : native_zleq 0 i = true) :
    native_zleq 0 (native_zplus i (native_nat_to_int w)) = true := by
  have hiNonneg : (0 : Int) ≤ i := by
    simpa [native_zleq] using hi
  have hwNonneg : (0 : Int) ≤ native_nat_to_int w := by
    unfold native_nat_to_int
    exact Int.natCast_nonneg w
  have hNonneg : (0 : Int) ≤ native_zplus i (native_nat_to_int w) := by
    unfold native_zplus
    exact Int.add_nonneg hiNonneg hwNonneg
  simpa [native_zleq] using hNonneg

private theorem native_zplus_nat_comm
    (i : native_Int) (w : native_Nat) :
    native_zplus (native_nat_to_int w) i =
      native_zplus i (native_nat_to_int w) := by
  simp [native_zplus, Int.add_comm]

/-- Simplifies EO-to-SMT translation for `repeat`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_repeat
    (x y : Term)
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.repeat y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.repeat y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.repeat y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.UOp1 UserOp1.repeat y) x) =
        SmtTerm.repeat (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hApplyNN : term_has_non_none_type (SmtTerm.repeat (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases repeat_args_of_non_none hApplyNN with ⟨i, w, hYNum, hX, hi⟩
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.repeat y) x)) =
        SmtType.BitVec (native_int_to_nat (native_zmult i (native_nat_to_int w))) := by
    rw [hTranslate, typeof_repeat_eq, hYNum, hX]
    simp [__smtx_typeof_repeat, native_ite, hi]
  have hYTerm : y = Term.Numeral i :=
    eo_to_smt_eq_numeral y i hYNum
  have hXEo :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w)) :=
    eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hX
  have hEo :
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.repeat y) x)) =
        SmtType.BitVec (native_int_to_nat (native_zmult i (native_nat_to_int w))) := by
    rw [hYTerm]
    change __eo_to_smt_type
        (__eo_typeof_repeat (Term.UOp UserOp.Int) (Term.Numeral i) (__eo_typeof x)) =
      SmtType.BitVec (native_int_to_nat (native_zmult i (native_nat_to_int w)))
    rw [hXEo]
    have hIGtZero : native_zlt (0 : native_Int) i = true := by
      have hi' : (1 : Int) ≤ i := by
        simpa [native_zleq] using hi
      have hlt : (0 : Int) < i := by
        omega
      simpa [native_zlt] using hlt
    simpa [__eo_typeof_repeat, __eo_requires, __eo_gt, __eo_mul,
      __eo_mk_apply, native_ite, native_teq, native_not, hIGtZero] using
        apply_eo_to_smt_type_bitvec_int_of_nonneg _
          (native_zleq_zero_zmult_nat_of_one_le i w hi)
  exact hSmt.trans hEo.symm

/-- Simplifies EO-to-SMT translation for `zero_extend`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_zero_extend
    (x y : Term)
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.zero_extend y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.zero_extend y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.zero_extend y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.UOp1 UserOp1.zero_extend y) x) =
        SmtTerm.zero_extend (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hApplyNN :
      term_has_non_none_type (SmtTerm.zero_extend (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases zero_extend_args_of_non_none hApplyNN with ⟨i, w, hYNum, hX, hi⟩
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.zero_extend y) x)) =
        SmtType.BitVec (native_int_to_nat (native_zplus i (native_nat_to_int w))) := by
    rw [hTranslate, typeof_zero_extend_eq, hYNum, hX]
    simp [__smtx_typeof_zero_extend, native_ite, hi]
  have hYTerm : y = Term.Numeral i :=
    eo_to_smt_eq_numeral y i hYNum
  have hXEo :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w)) :=
    eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hX
  have hEo :
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.zero_extend y) x)) =
        SmtType.BitVec (native_int_to_nat (native_zplus i (native_nat_to_int w))) := by
    rw [hYTerm]
    change __eo_to_smt_type
        (__eo_typeof_zero_extend (Term.UOp UserOp.Int) (Term.Numeral i) (__eo_typeof x)) =
      SmtType.BitVec (native_int_to_nat (native_zplus i (native_nat_to_int w)))
    rw [hXEo]
    have hIGtNegOne : native_zlt (-1 : native_Int) i = true :=
      native_zlt_neg_one_of_zleq_zero (n := i) hi
    simpa [__eo_typeof_zero_extend, __eo_requires, __eo_gt, __eo_add,
      __eo_mk_apply, native_ite, native_teq, native_not, hIGtNegOne,
      native_zplus_nat_comm i w] using
        apply_eo_to_smt_type_bitvec_int_of_nonneg _
          (native_zleq_zero_zplus_nat_right_of_nonneg i w hi)
  exact hSmt.trans hEo.symm

/-- Simplifies EO-to-SMT translation for `sign_extend`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_sign_extend
    (x y : Term)
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.sign_extend y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.sign_extend y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.sign_extend y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.UOp1 UserOp1.sign_extend y) x) =
        SmtTerm.sign_extend (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hApplyNN :
      term_has_non_none_type (SmtTerm.sign_extend (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases sign_extend_args_of_non_none hApplyNN with ⟨i, w, hYNum, hX, hi⟩
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.sign_extend y) x)) =
        SmtType.BitVec (native_int_to_nat (native_zplus i (native_nat_to_int w))) := by
    rw [hTranslate, typeof_sign_extend_eq, hYNum, hX]
    simp [__smtx_typeof_sign_extend, native_ite, hi]
  have hYTerm : y = Term.Numeral i :=
    eo_to_smt_eq_numeral y i hYNum
  have hXEo :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w)) :=
    eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hX
  have hEo :
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.sign_extend y) x)) =
        SmtType.BitVec (native_int_to_nat (native_zplus i (native_nat_to_int w))) := by
    rw [hYTerm]
    change __eo_to_smt_type
        (__eo_typeof_zero_extend (Term.UOp UserOp.Int) (Term.Numeral i) (__eo_typeof x)) =
      SmtType.BitVec (native_int_to_nat (native_zplus i (native_nat_to_int w)))
    rw [hXEo]
    have hIGtNegOne : native_zlt (-1 : native_Int) i = true :=
      native_zlt_neg_one_of_zleq_zero (n := i) hi
    simpa [__eo_typeof_zero_extend, __eo_requires, __eo_gt, __eo_add,
      __eo_mk_apply, native_ite, native_teq, native_not, hIGtNegOne,
      native_zplus_nat_comm i w] using
        apply_eo_to_smt_type_bitvec_int_of_nonneg _
          (native_zleq_zero_zplus_nat_right_of_nonneg i w hi)
  exact hSmt.trans hEo.symm

/-- Simplifies EO-to-SMT translation for `rotate_left`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_rotate_left
    (x y : Term)
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.rotate_left y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.rotate_left y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.rotate_left y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.UOp1 UserOp1.rotate_left y) x) =
        SmtTerm.rotate_left (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hApplyNN :
      term_has_non_none_type (SmtTerm.rotate_left (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases rotate_left_args_of_non_none hApplyNN with ⟨i, w, hYNum, hX, hi⟩
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.rotate_left y) x)) =
        SmtType.BitVec w := by
    rw [hTranslate, typeof_rotate_left_eq, hYNum, hX]
    simp [__smtx_typeof_rotate_left, native_ite, hi]
  have hYTerm : y = Term.Numeral i :=
    eo_to_smt_eq_numeral y i hYNum
  have hXEo :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w)) :=
    eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hX
  have hEo :
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.rotate_left y) x)) =
        SmtType.BitVec w := by
    rw [hYTerm]
    change __eo_to_smt_type
        (__eo_typeof_rotate_left (Term.UOp UserOp.Int) (Term.Numeral i) (__eo_typeof x)) =
      SmtType.BitVec w
    rw [hXEo]
    have hIGtNegOne : native_zlt (-1 : native_Int) i = true :=
      native_zlt_neg_one_of_zleq_zero (n := i) hi
    simpa [__eo_typeof_rotate_left, __eo_requires, __eo_gt, native_ite,
      native_teq, native_not, hIGtNegOne] using
        apply_eo_to_smt_type_bitvec_nat w
  exact hSmt.trans hEo.symm

/-- Simplifies EO-to-SMT translation for `rotate_right`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_rotate_right
    (x y : Term)
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.rotate_right y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.rotate_right y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.rotate_right y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.UOp1 UserOp1.rotate_right y) x) =
        SmtTerm.rotate_right (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hApplyNN :
      term_has_non_none_type (SmtTerm.rotate_right (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases rotate_right_args_of_non_none hApplyNN with ⟨i, w, hYNum, hX, hi⟩
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.rotate_right y) x)) =
        SmtType.BitVec w := by
    rw [hTranslate, typeof_rotate_right_eq, hYNum, hX]
    simp [__smtx_typeof_rotate_right, native_ite, hi]
  have hYTerm : y = Term.Numeral i :=
    eo_to_smt_eq_numeral y i hYNum
  have hXEo :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w)) :=
    eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hX
  have hEo :
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.rotate_right y) x)) =
        SmtType.BitVec w := by
    rw [hYTerm]
    change __eo_to_smt_type
        (__eo_typeof_rotate_left (Term.UOp UserOp.Int) (Term.Numeral i) (__eo_typeof x)) =
      SmtType.BitVec w
    rw [hXEo]
    have hIGtNegOne : native_zlt (-1 : native_Int) i = true :=
      native_zlt_neg_one_of_zleq_zero (n := i) hi
    simpa [__eo_typeof_rotate_left, __eo_requires, __eo_gt, native_ite,
      native_teq, native_not, hIGtNegOne] using
        apply_eo_to_smt_type_bitvec_nat w
  exact hSmt.trans hEo.symm

/-- Simplifies EO-to-SMT translation for `int_to_bv`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_int_to_bv
    (x y : Term)
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.int_to_bv y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv y) x) =
        SmtTerm.int_to_bv (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hApplyNN :
      term_has_non_none_type (SmtTerm.int_to_bv (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases int_to_bv_args_of_non_none hApplyNN with ⟨i, hYNum, hX, hi⟩
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv y) x)) =
        SmtType.BitVec (native_int_to_nat i) := by
    rw [hTranslate, typeof_int_to_bv_eq, hYNum, hX]
    simp [__smtx_typeof_int_to_bv, native_ite, hi]
  have hYTerm : y = Term.Numeral i :=
    eo_to_smt_eq_numeral y i hYNum
  have hXEo : __eo_typeof x = Term.UOp UserOp.Int :=
    eo_typeof_eq_int_of_smt_int_from_ih x ihX hX
  have hEo :
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.int_to_bv y) x)) =
        SmtType.BitVec (native_int_to_nat i) := by
    rw [hYTerm]
    change __eo_to_smt_type
        (__eo_typeof_int_to_bv (Term.UOp UserOp.Int) (Term.Numeral i) (__eo_typeof x)) =
      SmtType.BitVec (native_int_to_nat i)
    rw [hXEo]
    have hIGtNegOne : native_zlt (-1 : native_Int) i = true :=
      native_zlt_neg_one_of_zleq_zero (n := i) hi
    simpa [__eo_typeof_int_to_bv, __eo_requires, __eo_gt, native_ite,
      native_teq, native_not, hIGtNegOne] using
        apply_eo_to_smt_type_bitvec_int_of_nonneg i hi
  exact hSmt.trans hEo.symm

/-- Simplifies EO-to-SMT translation for `_at_bit`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_at_bit
    (x y : Term)
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1._at_bit y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1._at_bit y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp1 UserOp1._at_bit y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.UOp1 UserOp1._at_bit y) x) =
        SmtTerm.eq
          (SmtTerm.extract (__eo_to_smt y) (__eo_to_smt y) (__eo_to_smt x))
          (SmtTerm.Binary 1 1) := by
    rfl
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.eq
          (SmtTerm.extract (__eo_to_smt y) (__eo_to_smt y) (__eo_to_smt x))
          (SmtTerm.Binary 1 1)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  have hEqNN :
      __smtx_typeof_eq
          (__smtx_typeof (SmtTerm.extract (__eo_to_smt y) (__eo_to_smt y) (__eo_to_smt x)))
          (SmtType.BitVec 1) ≠
        SmtType.None := by
    unfold term_has_non_none_type at hApplyNN
    rw [typeof_eq_eq, typeof_binary_one_eq] at hApplyNN
    exact hApplyNN
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1._at_bit y) x)) =
        SmtType.Bool := by
    rw [hTranslate, typeof_eq_eq, typeof_binary_one_eq]
    cases hExt : __smtx_typeof (SmtTerm.extract (__eo_to_smt y) (__eo_to_smt y) (__eo_to_smt x)) <;>
      simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq, hExt] at hEqNN ⊢
    exact hEqNN
  have hExtTy :
      __smtx_typeof (SmtTerm.extract (__eo_to_smt y) (__eo_to_smt y) (__eo_to_smt x)) =
        SmtType.BitVec 1 :=
    by
      by_cases hNone :
          __smtx_typeof (SmtTerm.extract (__eo_to_smt y) (__eo_to_smt y) (__eo_to_smt x)) =
            SmtType.None
      · exfalso
        exact hEqNN (by
          rw [hNone]
          simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq])
      · by_cases hEq :
          __smtx_typeof (SmtTerm.extract (__eo_to_smt y) (__eo_to_smt y) (__eo_to_smt x)) =
            SmtType.BitVec 1
        · exact hEq
        · exfalso
          exact hEqNN (by
            simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq, hNone, hEq])
  have hExtNN :
      term_has_non_none_type (SmtTerm.extract (__eo_to_smt y) (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [hExtTy]
    simp
  rcases extract_args_of_non_none hExtNN with ⟨i, _j, w, hYNum, _hYNum', hX, _hj0, _hji, _hiw⟩
  have hYSmt : __smtx_typeof (__eo_to_smt y) = SmtType.Int := by
    rw [hYNum]
    unfold __smtx_typeof
    rfl
  have hYTerm : y = Term.Numeral i :=
    eo_to_smt_eq_numeral y i hYNum
  have hYEo : __eo_typeof y = Term.UOp UserOp.Int := by
    rw [hYTerm]
    rfl
  have hXEo :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w)) :=
    eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hX
  have hEo :
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp1 UserOp1._at_bit y) x)) =
        SmtType.Bool := by
    change __eo_to_smt_type (__eo_typeof__at_bit (__eo_typeof y) (__eo_typeof x)) =
      SmtType.Bool
    rw [hYEo, hXEo]
    rfl
  exact hSmt.trans hEo.symm

/-- Simplifies EO-to-SMT translation for `_at_from_bools`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_at_from_bools
    (x y : Term)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) y) x)) := by
  let bit :=
    SmtTerm.ite (__eo_to_smt y) (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) y) x) =
        SmtTerm.concat (__eo_to_smt x) bit := by
    rfl
  have hApplyNN : term_has_non_none_type (SmtTerm.concat (__eo_to_smt x) bit) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases bv_concat_args_of_non_none hApplyNN with ⟨w1, w2, hX, hBit⟩
  have hBitNN : term_has_non_none_type bit := by
    unfold term_has_non_none_type
    rw [hBit]
    simp
  rcases ite_args_of_non_none hBitNN with ⟨T, hY, hThen, hElse, hT⟩
  have hBitTy : __smtx_typeof bit = T := by
    rw [show bit =
        SmtTerm.ite (__eo_to_smt y) (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0) by rfl]
    rw [typeof_ite_eq, hY, hThen, hElse]
    simp [__smtx_typeof_ite, native_ite, native_Teq]
  have hThenNN : __smtx_typeof (SmtTerm.Binary 1 1) ≠ SmtType.None := by
    rw [hThen]
    exact hT
  have hTBitVec1 : T = SmtType.BitVec 1 :=
    hThen.symm.trans (smtx_typeof_binary_of_non_none 1 1 hThenNN)
  have hW2 : w2 = 1 := by
    have hEq : SmtType.BitVec w2 = SmtType.BitVec 1 :=
      hBit.symm.trans (hBitTy.trans hTBitVec1)
    cases hEq
    rfl
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) y) x)) =
        SmtType.BitVec
          (native_int_to_nat (native_zplus (native_nat_to_int w1) (native_nat_to_int w2))) := by
    rw [hTranslate, typeof_concat_eq (__eo_to_smt x) bit]
    simp [__smtx_typeof_concat, hBit, hX]
  have hYEo : __eo_typeof y = Term.Bool :=
    eo_typeof_eq_bool_of_smt_bool_from_ih y ihY hY
  have hXEo :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w1)) :=
    eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w1 hX
  have hEo :
      __eo_to_smt_type
          (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) y) x)) =
        SmtType.BitVec
          (native_int_to_nat (native_zplus (native_nat_to_int w1) (native_nat_to_int w2))) := by
    change
      __eo_to_smt_type (__eo_typeof__at_from_bools (__eo_typeof y) (__eo_typeof x)) =
        SmtType.BitVec
          (native_int_to_nat (native_zplus (native_nat_to_int w1) (native_nat_to_int w2)))
    rw [hYEo, hXEo, hW2]
    have hNonnegProp : (0 : Int) ≤ native_zplus 1 (native_nat_to_int w1) := by
      unfold native_zplus native_nat_to_int
      exact Int.add_nonneg (by decide) (Int.natCast_nonneg w1)
    have hNonneg : native_zleq 0 (native_zplus 1 (native_nat_to_int w1)) = true := by
      unfold native_zleq
      simp [hNonnegProp]
    change
      native_ite (native_zleq 0 (native_zplus 1 (native_nat_to_int w1)))
        (SmtType.BitVec (native_int_to_nat (native_zplus 1 (native_nat_to_int w1))))
      SmtType.None =
      SmtType.BitVec
        (native_int_to_nat (native_zplus (native_nat_to_int w1) (native_nat_to_int 1)))
    rw [hNonneg]
    simp [native_ite, native_zplus, native_nat_to_int,
      native_int_to_nat, Int.add_comm]
  exact hSmt.trans hEo.symm

/-- Computes `__smtx_typeof` for `eq_non_none`. -/
theorem smtx_typeof_eq_non_none
    {T U : SmtType}
    (h : __smtx_typeof_eq T U ≠ SmtType.None) :
    T = U ∧ T ≠ SmtType.None := by
  by_cases hNone : T = SmtType.None
  · subst hNone
    exfalso
    exact h (by simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq])
  · by_cases hEq : T = U
    · exact ⟨hEq, hNone⟩
    · exfalso
      exact h (by
        simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq, hNone, hEq])

/-- Recovers Boolean typing of a zero-index `choice_nth` body from `non_none`. -/
theorem choice_nth_body_bool_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.choice s T body)) :
    __smtx_typeof body = SmtType.Bool := by
  unfold term_has_non_none_type at ht
  by_cases hEq : native_Teq (__smtx_typeof body) SmtType.Bool = true
  · simpa [native_Teq] using hEq
  · have hEqFalse : native_Teq (__smtx_typeof body) SmtType.Bool = false := by
      cases hTest : native_Teq (__smtx_typeof body) SmtType.Bool <;> simp [hTest] at hEq ⊢
    exfalso
    apply ht
    unfold __smtx_typeof
    simp [hEqFalse, native_ite]

def smtStringsNumOccur
    (replace : SmtTerm → SmtTerm → SmtTerm → SmtTerm)
    (source pattern : SmtTerm) : SmtTerm :=
  let zero := SmtTerm.Numeral 0
  SmtTerm.neg
    (SmtTerm.str_len
      (replace source pattern (SmtTerm.str_substr source zero (SmtTerm.Numeral 1))))
    (SmtTerm.str_len
      (replace source pattern (SmtTerm.str_substr source zero zero)))

def smtStringsOccurIndex
    (replace : SmtTerm → SmtTerm → SmtTerm → SmtTerm)
    (source pattern count : SmtTerm) : SmtTerm :=
  let zero := SmtTerm.Numeral 0
  let one := SmtTerm.Numeral 1
  let index := SmtTerm.Var (native_string_lit "@x") SmtType.Int
  let previous := SmtTerm.str_substr source zero (SmtTerm.neg index one)
  let pref := SmtTerm.str_substr source zero index
  SmtTerm.choice (native_string_lit "@x") SmtType.Int
    (SmtTerm.and (SmtTerm.geq index zero)
      (SmtTerm.and
        (SmtTerm.eq (smtStringsNumOccur replace pref pattern) count)
        (SmtTerm.or (SmtTerm.eq index zero)
          (SmtTerm.lt (smtStringsNumOccur replace previous pattern) count))))

theorem eo_to_smt_strings_num_occur_eq (x y : Term) :
    __eo_to_smt
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_strings_num_occur) x) y) =
      smtStringsNumOccur SmtTerm.str_replace_all
        (__eo_to_smt x) (__eo_to_smt y) :=
by
  rfl

theorem eo_to_smt_strings_num_occur_re_eq (x y : Term) :
    __eo_to_smt
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_strings_num_occur_re) x) y) =
      smtStringsNumOccur SmtTerm.str_replace_re_all
        (__eo_to_smt x) (__eo_to_smt y) :=
by
  rfl

theorem eo_to_smt_strings_occur_index_eq (x y z : Term) :
    __eo_to_smt
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at_strings_occur_index) x) y)
          z) =
      SmtTerm._at_strings_occur_index
        (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z) :=
by
  rfl

theorem eo_to_smt_strings_occur_index_re_eq (x y z : Term) :
    __eo_to_smt
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at_strings_occur_index_re) x) y)
          z) =
      SmtTerm._at_strings_occur_index_re
        (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z) :=
by
  rfl

theorem eo_to_smt_strings_replace_all_result_eq (w z y x : Term) :
    __eo_to_smt
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.UOp UserOp._at_strings_replace_all_result) w)
              z)
            y)
          x) =
      SmtTerm.str_replace_all
        (SmtTerm.str_substr (__eo_to_smt w)
          (SmtTerm._at_strings_occur_index
            (__eo_to_smt w) (__eo_to_smt z) (__eo_to_smt x))
          (SmtTerm.str_len (__eo_to_smt w)))
        (__eo_to_smt z) (__eo_to_smt y) :=
by
  rfl

theorem eo_to_smt_strings_replace_re_all_result_eq (w z y x : Term) :
    __eo_to_smt
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.UOp UserOp._at_strings_replace_re_all_result) w)
              z)
            y)
          x) =
      SmtTerm.str_replace_re_all
        (SmtTerm.str_substr (__eo_to_smt w)
          (SmtTerm._at_strings_occur_index_re
            (__eo_to_smt w) (__eo_to_smt z) (__eo_to_smt x))
          (SmtTerm.str_len (__eo_to_smt w)))
        (__eo_to_smt z) (__eo_to_smt y) :=
by
  rfl

theorem eo_to_smt_apply_apply_apply_apply_eq_of_head_not_uop
    (g y x z body : Term)
    (hNotUOp : ∀ op, g ≠ Term.UOp op) :
    __eo_to_smt
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply g y) x)
            z)
          body) =
      SmtTerm.Apply
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.Apply g y) x)
            z))
        (__eo_to_smt body) :=
by
  cases g
  case UOp op =>
    exact False.elim (hNotUOp op rfl)
  all_goals
    rfl

theorem eo_to_smt_apply_apply_apply_apply_uop_generic_eq
    (op : UserOp) (w z y x : Term)
    (hNotReplaceAllResult :
      op ≠ UserOp._at_strings_replace_all_result)
    (hNotReplaceReAllResult :
      op ≠ UserOp._at_strings_replace_re_all_result) :
    __eo_to_smt
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp op) w) z)
            y)
          x) =
      SmtTerm.Apply
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp op) w) z)
            y))
        (__eo_to_smt x) :=
by
  cases op
  case _at_strings_replace_all_result =>
    exact False.elim (hNotReplaceAllResult rfl)
  case _at_strings_replace_re_all_result =>
    exact False.elim (hNotReplaceReAllResult rfl)
  all_goals
    rfl

private theorem smt_strings_num_occur_type_and_first_replace_non_none
    (replace : SmtTerm → SmtTerm → SmtTerm → SmtTerm)
    (source pattern : SmtTerm)
    (hNonNone : term_has_non_none_type (smtStringsNumOccur replace source pattern)) :
    __smtx_typeof (smtStringsNumOccur replace source pattern) = SmtType.Int ∧
      term_has_non_none_type
        (replace source pattern
          (SmtTerm.str_substr source (SmtTerm.Numeral 0) (SmtTerm.Numeral 1))) := by
  let first :=
    replace source pattern
      (SmtTerm.str_substr source (SmtTerm.Numeral 0) (SmtTerm.Numeral 1))
  let second :=
    replace source pattern
      (SmtTerm.str_substr source (SmtTerm.Numeral 0) (SmtTerm.Numeral 0))
  have hArgs :=
    arith_binop_args_of_non_none (op := SmtTerm.neg)
      (typeof_neg_eq (SmtTerm.str_len first) (SmtTerm.str_len second))
      (by simpa [smtStringsNumOccur, first, second] using hNonNone)
  rcases hArgs with hArgs | hArgs
  · have hTy :
        __smtx_typeof (smtStringsNumOccur replace source pattern) = SmtType.Int := by
      simp [smtStringsNumOccur, first, second, typeof_neg_eq,
        __smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
    have hFirstLenNN : term_has_non_none_type (SmtTerm.str_len first) := by
      unfold term_has_non_none_type
      rw [hArgs.1]
      simp
    rcases seq_arg_of_non_none_ret (op := SmtTerm.str_len)
        (typeof_str_len_eq first) hFirstLenNN with ⟨T, hFirst⟩
    exact ⟨hTy, by
      unfold term_has_non_none_type
      rw [hFirst]
      simp⟩
  · have hFirstLenNN : term_has_non_none_type (SmtTerm.str_len first) := by
      unfold term_has_non_none_type
      rw [hArgs.1]
      simp
    rcases seq_arg_of_non_none_ret (op := SmtTerm.str_len)
        (typeof_str_len_eq first) hFirstLenNN with ⟨T, hFirst⟩
    have hFirstLenInt : __smtx_typeof (SmtTerm.str_len first) = SmtType.Int := by
      rw [typeof_str_len_eq, hFirst]
      rfl
    rw [hArgs.1] at hFirstLenInt
    cases hFirstLenInt

theorem smt_strings_num_occur_args_of_non_none
    (source pattern : SmtTerm)
    (hNonNone :
      term_has_non_none_type
        (smtStringsNumOccur SmtTerm.str_replace_all source pattern)) :
    ∃ T : SmtType,
      __smtx_typeof source = SmtType.Seq T ∧
        __smtx_typeof pattern = SmtType.Seq T ∧
        __smtx_typeof
            (smtStringsNumOccur SmtTerm.str_replace_all source pattern) =
          SmtType.Int := by
  rcases smt_strings_num_occur_type_and_first_replace_non_none
      SmtTerm.str_replace_all source pattern hNonNone with
    ⟨hCount, hReplace⟩
  rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace_all)
      (typeof_str_replace_all_eq source pattern
        (SmtTerm.str_substr source (SmtTerm.Numeral 0) (SmtTerm.Numeral 1)))
      hReplace with
    ⟨T, hSource, hPattern, _hReplacement⟩
  exact ⟨T, hSource, hPattern, hCount⟩

theorem smt_strings_num_occur_re_args_of_non_none
    (source pattern : SmtTerm)
    (hNonNone :
      term_has_non_none_type
        (smtStringsNumOccur SmtTerm.str_replace_re_all source pattern)) :
    __smtx_typeof source = SmtType.Seq SmtType.Char ∧
      __smtx_typeof pattern = SmtType.RegLan ∧
      __smtx_typeof
          (smtStringsNumOccur SmtTerm.str_replace_re_all source pattern) =
        SmtType.Int := by
  rcases smt_strings_num_occur_type_and_first_replace_non_none
      SmtTerm.str_replace_re_all source pattern hNonNone with
    ⟨hCount, hReplace⟩
  have hArgs :=
    str_replace_re_args_of_non_none (op := SmtTerm.str_replace_re_all)
      (typeof_str_replace_re_all_eq source pattern
        (SmtTerm.str_substr source (SmtTerm.Numeral 0) (SmtTerm.Numeral 1)))
      hReplace
  exact ⟨hArgs.1, hArgs.2.1, hCount⟩

theorem smt_strings_occur_index_args_of_non_none
    (source pattern count : SmtTerm)
    (hNonNone :
      term_has_non_none_type
        (SmtTerm._at_strings_occur_index source pattern count)) :
    ∃ T : SmtType,
      __smtx_typeof source = SmtType.Seq T ∧
        __smtx_typeof pattern = SmtType.Seq T ∧
        __smtx_typeof count = SmtType.Int ∧
        __smtx_typeof
            (SmtTerm._at_strings_occur_index source pattern count) =
          SmtType.Int := by
  have hTy :
      __smtx_typeof (SmtTerm._at_strings_occur_index source pattern count) =
        __smtx_typeof_str_indexof (__smtx_typeof source)
          (__smtx_typeof pattern) (__smtx_typeof count) := by
    rw [__smtx_typeof.eq_def] <;> simp only
  unfold term_has_non_none_type at hNonNone
  rw [hTy] at hNonNone
  have hArgs :
      ∃ T : SmtType,
        __smtx_typeof source = SmtType.Seq T ∧
          __smtx_typeof pattern = SmtType.Seq T ∧
          __smtx_typeof count = SmtType.Int := by
    unfold __smtx_typeof_str_indexof at hNonNone
    split at hNonNone
    · rename_i x1 x2 h1 h2 h3
      by_cases hEq : native_Teq x1 x2
      · have hx : x1 = x2 := by simpa [native_Teq] using hEq
        subst hx
        exact ⟨x1, h1, h2, h3⟩
      · exfalso
        apply hNonNone
        rw [native_ite, if_neg hEq]
    · exact absurd rfl hNonNone
  rcases hArgs with ⟨T, h1, h2, h3⟩
  refine ⟨T, h1, h2, h3, ?_⟩
  rw [hTy, h1, h2, h3]
  simp [__smtx_typeof_str_indexof, native_ite, native_Teq]

theorem smt_strings_occur_index_re_args_of_non_none
    (source pattern count : SmtTerm)
    (hNonNone :
      term_has_non_none_type
        (SmtTerm._at_strings_occur_index_re source pattern count)) :
    __smtx_typeof source = SmtType.Seq SmtType.Char ∧
      __smtx_typeof pattern = SmtType.RegLan ∧
      __smtx_typeof count = SmtType.Int ∧
      __smtx_typeof
          (SmtTerm._at_strings_occur_index_re source pattern count) =
        SmtType.Int := by
  have hTy :
      __smtx_typeof
          (SmtTerm._at_strings_occur_index_re source pattern count) =
        native_ite
          (native_Teq (__smtx_typeof source) (SmtType.Seq SmtType.Char))
          (native_ite (native_Teq (__smtx_typeof pattern) SmtType.RegLan)
            (native_ite (native_Teq (__smtx_typeof count) SmtType.Int)
              SmtType.Int SmtType.None)
            SmtType.None)
          SmtType.None := by
    rw [__smtx_typeof.eq_def] <;> simp only
  unfold term_has_non_none_type at hNonNone
  rw [hTy] at hNonNone
  by_cases h1 : native_Teq (__smtx_typeof source) (SmtType.Seq SmtType.Char)
  · by_cases h2 : native_Teq (__smtx_typeof pattern) SmtType.RegLan
    · by_cases h3 : native_Teq (__smtx_typeof count) SmtType.Int
      · refine ⟨by simpa [native_Teq] using h1,
          by simpa [native_Teq] using h2,
          by simpa [native_Teq] using h3, ?_⟩
        rw [hTy]
        simp [native_ite, h1, h2, h3]
      · exfalso
        apply hNonNone
        simp [native_ite, h1, h2, h3]
    · exfalso
      apply hNonNone
      simp [native_ite, h1, h2]
  · exfalso
    apply hNonNone
    simp [native_ite, h1]


/-- Simplifies EO-to-SMT translation for `_at_strings_deq_diff`. -/
theorem eo_to_smt_typeof_matches_translation_apply_at_strings_deq_diff
    (x y : Term)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt (Term._at_strings_deq_diff y x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt (Term._at_strings_deq_diff y x)) =
      __eo_to_smt_type
        (__eo_typeof (Term._at_strings_deq_diff y x)) ∧
      eo_type_valid (__eo_typeof (Term._at_strings_deq_diff y x)) := by
  have hTranslate :
      __eo_to_smt (Term._at_strings_deq_diff y x) =
        SmtTerm.seq_diff (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hArgsNN :
      term_has_non_none_type (SmtTerm.seq_diff (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases seq_binop_args_of_non_none_ret (op := SmtTerm.seq_diff)
      (typeof_seq_diff_eq (__eo_to_smt y) (__eo_to_smt x)) hArgsNN with ⟨A, hYSeq, hXSeq⟩
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term._at_strings_deq_diff y x)) =
        SmtType.Int := by
    rw [hTranslate, typeof_seq_diff_eq]
    simp [__smtx_typeof_seq_op_2_ret, native_ite, native_Teq, hYSeq, hXSeq]
  have hAWF :
      smtx_type_field_wf_rec A native_reflist_nil :=
    smtx_seq_component_field_wf_rec_of_non_none_type_apply (__eo_to_smt y) A hYSeq
  have hANN : A ≠ SmtType.None := by
    intro hNone
    subst A
    simp [smtx_type_field_wf_rec, __smtx_type_wf_rec] at hAWF
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih y ihY hYSeq with ⟨U, hYU, hU⟩
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih x ihX hXSeq with ⟨V, hXV, hV⟩
  have hVU : V = U :=
    eo_to_smt_type_injective_of_field_wf_rec hV hU hAWF
  have hXU : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) U := by
    rw [hXV, hVU]
  have hUNN : __eo_to_smt_type U ≠ SmtType.None := by
    rw [hU]
    exact hANN
  have hUNS : U ≠ Term.Stuck :=
    eo_term_ne_stuck_of_smt_type_non_none U hUNN
  have hEo :
      __eo_to_smt_type (__eo_typeof (Term._at_strings_deq_diff y x)) =
        SmtType.Int := by
    change __eo_to_smt_type (__eo_typeof__at_strings_deq_diff (__eo_typeof y) (__eo_typeof x)) =
      SmtType.Int
    rw [hYU, hXU]
    simpa [__eo_typeof__at_strings_deq_diff] using
      congrArg __eo_to_smt_type
        (eo_requires_eo_eq_self_of_non_stuck U (Term.UOp UserOp.Int) hUNS)
  refine ⟨hSmt.trans hEo.symm, ?_⟩
  rw [eo_to_smt_type_eq_int hEo]
  simp [eo_type_valid, noNoneTy]

/-- Simplifies EO-to-SMT translation for `_at_strings_num_occur`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_at_strings_num_occur
    (x y : Term)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_num_occur) y) x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_num_occur) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_num_occur) y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_num_occur) y) x) =
        smtStringsNumOccur SmtTerm.str_replace_all (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hCountNN :
      term_has_non_none_type
        (smtStringsNumOccur SmtTerm.str_replace_all
          (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases smt_strings_num_occur_args_of_non_none
      (__eo_to_smt y) (__eo_to_smt x) hCountNN with
    ⟨T, hHaystackSeq, hNeedleSeq, hCountTy⟩
  have hSmt :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_num_occur) y) x)) =
        SmtType.Int := by
    rw [hTranslate]
    exact hCountTy
  have hTWF :
      smtx_type_field_wf_rec T native_reflist_nil :=
    smtx_seq_component_field_wf_rec_of_non_none_type_apply
      (__eo_to_smt y) T hHaystackSeq
  have hTNN : T ≠ SmtType.None := by
    intro hNone
    subst T
    simp [smtx_type_field_wf_rec, __smtx_type_wf_rec] at hTWF
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih y ihY hHaystackSeq with
    ⟨U, hYU, hU⟩
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih x ihX hNeedleSeq with
    ⟨V, hXV, hV⟩
  have hVU : V = U :=
    eo_to_smt_type_injective_of_field_wf_rec hV hU hTWF
  have hXU : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) U := by
    rw [hXV, hVU]
  have hUNN : __eo_to_smt_type U ≠ SmtType.None := by
    rw [hU]
    exact hTNN
  have hUNS : U ≠ Term.Stuck :=
    eo_term_ne_stuck_of_smt_type_non_none U hUNN
  have hEo :
      __eo_to_smt_type
          (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_num_occur) y) x)) =
        SmtType.Int := by
    change __eo_to_smt_type (__eo_typeof__at_strings_deq_diff (__eo_typeof y) (__eo_typeof x)) =
      SmtType.Int
    rw [hYU, hXU]
    simpa [__eo_typeof__at_strings_deq_diff] using
      congrArg __eo_to_smt_type
        (eo_requires_eo_eq_self_of_non_stuck U (Term.UOp UserOp.Int) hUNS)
  exact hSmt.trans hEo.symm

private theorem eo_to_smt_typeof_matches_translation_apply_at_strings_num_occur_re
    (x y : Term)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_num_occur_re) y) x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_num_occur_re) y) x)) =
      __eo_to_smt_type
        (__eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_num_occur_re) y) x)) := by
  have hTranslate :
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_num_occur_re) y) x) =
        smtStringsNumOccur SmtTerm.str_replace_re_all
          (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hCountNN :
      term_has_non_none_type
        (smtStringsNumOccur SmtTerm.str_replace_re_all
          (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  have hArgs :=
    smt_strings_num_occur_re_args_of_non_none
      (__eo_to_smt y) (__eo_to_smt x) hCountNN
  have hSmt :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_num_occur_re) y) x)) =
        SmtType.Int := by
    rw [hTranslate]
    exact hArgs.2.2
  have hYEo : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) :=
    eo_typeof_eq_seq_char_of_smt_seq_char_from_ih y ihY hArgs.1
  have hXEo : __eo_typeof x = Term.UOp UserOp.RegLan :=
    eo_typeof_eq_reglan_of_smt_reglan_from_ih x ihX hArgs.2.1
  have hEo :
      __eo_to_smt_type
          (__eo_typeof
            (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_num_occur_re) y) x)) =
        SmtType.Int := by
    change
      __eo_to_smt_type
          (__eo_typeof__at_strings_num_occur_re (__eo_typeof y) (__eo_typeof x)) =
        SmtType.Int
    rw [hYEo, hXEo]
    rfl
  exact hSmt.trans hEo.symm

/-- The only EO terms that translate to bare SMT datatype constructors are
datatype constructors and the built-in unit tuple value. -/
theorem eo_to_smt_eq_dt_cons_cases
    (y : Term) (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat)
    (hy : __eo_to_smt y = SmtTerm.DtCons s d i) :
    (∃ d0, d = __eo_to_smt_datatype_decl d0 ∧ y = Term.DtCons s d0 i ∧
      __eo_reserved_datatype_name s = false) ∨
      (s = (native_string_lit "@Tuple") ∧
        d = __eo_to_smt_tuple_decl
          (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null) ∧
        i = native_nat_zero ∧ y = Term.UOp UserOp.tuple_unit) := by
  cases y
  case DtCons s0 d0 i0 =>
    cases hReserved : __eo_reserved_datatype_name s0
    · simp [eo_to_smt_term_dt_cons, native_ite, hReserved] at hy
      rcases hy with ⟨hs, hd, hi⟩
      cases hs
      cases hd
      cases hi
      exact Or.inl ⟨d0, rfl, rfl, hReserved⟩
    · simp [eo_to_smt_term_dt_cons, native_ite, hReserved] at hy
  case UOp op =>
    by_cases hop : op = UserOp.tuple_unit
    · subst op
      cases hy
      exact Or.inr ⟨rfl, rfl, rfl, rfl⟩
    · exfalso
      cases op
      all_goals
        first
        | exact hop rfl
        | change SmtTerm.None = SmtTerm.DtCons s d i at hy
          cases hy
        | change SmtTerm.re_allchar = SmtTerm.DtCons s d i at hy
          cases hy
        | change SmtTerm.re_none = SmtTerm.DtCons s d i at hy
          cases hy
        | change SmtTerm.re_all = SmtTerm.DtCons s d i at hy
          cases hy
  case UOp1 op z =>
    cases op <;> try (exfalso; cases hy)
    case seq_empty =>
      exfalso
      change __eo_to_smt_seq_empty (__eo_to_smt_type z) = SmtTerm.DtCons s d i at hy
      cases hTy : __eo_to_smt_type z <;> simp [__eo_to_smt_seq_empty, hTy] at hy
    case set_empty =>
      exfalso
      change __eo_to_smt_set_empty (__eo_to_smt_type z) = SmtTerm.DtCons s d i at hy
      cases hTy : __eo_to_smt_type z <;> simp [__eo_to_smt_set_empty, hTy] at hy
  case Apply f x =>
    exact (eo_to_smt_apply_ne_dt_cons f x s d i hy).elim
  case UOp2 op q idx =>
    cases op <;> try (exfalso; cases hy)
    case _at_quantifiers_skolemize =>
      exact (eo_to_smt_quant_skolemize_top_ne_dt_cons q idx s d i hy).elim
    case _at_const =>
      exact (eo_to_smt_at_const_ne_dt_cons q idx s d i hy).elim
  case UOp3 op t r idx =>
    cases op
    case _at_re_unfold_pos_component =>
      exfalso
      change native_ite (__eo_to_smt_nat_is_valid idx)
          (__eo_to_smt_re_unfold_pos_component (__eo_to_smt t) (__eo_to_smt r)
            (__eo_to_smt_nat idx))
          SmtTerm.None =
        SmtTerm.DtCons s d i at hy
      unfold native_ite at hy
      split at hy <;> try cases hy
      exact eo_to_smt_re_unfold_ne_dt_cons _ _ _ _ _ _ hy
    case _at_witness_string_length =>
      exfalso
      change native_ite (__eo_to_smt_nat_is_valid r)
          (native_ite (__eo_to_smt_nat_is_valid idx)
            (SmtTerm.choice (native_string_lit "@x") (__eo_to_smt_type t)
              (SmtTerm.eq
                (SmtTerm.str_len (SmtTerm.Var (native_string_lit "@x") (__eo_to_smt_type t)))
                (__eo_to_smt r))) SmtTerm.None) SmtTerm.None =
        SmtTerm.DtCons s d i at hy
      unfold native_ite at hy
      split at hy <;> try cases hy
      split at hy <;> cases hy
  case Var name T =>
    exfalso
    cases name <;> cases hy
  case DtSel s0 d0 i0 j0 =>
    exfalso
    cases hReserved : __eo_reserved_datatype_name s0 <;>
      simp [eo_to_smt_term_dt_sel, native_ite, hReserved] at hy
  all_goals
    exfalso
    cases hy

/-- Datatype tester EO typing returns Bool when both inputs are defined. -/
private theorem eo_typeof_is_bool_of_non_stuck
    (C D : Term) (hC : C ≠ Term.Stuck) (hD : D ≠ Term.Stuck) :
    __eo_typeof_is C D = Term.Bool := by
  cases C <;> cases D <;> simp [__eo_typeof_is] at hC hD ⊢

/-- Simplifies EO-to-SMT translation for datatype testers. -/
private theorem eo_to_smt_typeof_matches_translation_apply_is
    (x y : Term)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.is y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.is y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.is y) x)) := by
  cases hCons : __eo_to_smt y with
  | DtCons s d i =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp1 UserOp1.is y) x) =
            SmtTerm.Apply (SmtTerm.DtTester s d i) (__eo_to_smt x) := by
        change SmtTerm.Apply (__eo_to_smt_tester (__eo_to_smt y)) (__eo_to_smt x) =
          SmtTerm.Apply (SmtTerm.DtTester s d i) (__eo_to_smt x)
        rw [hCons]
        simp [__eo_to_smt_tester]
      have hApplyNN :
          term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtTester s d i) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.is y) x)) =
            SmtType.Bool := by
        rw [hTranslate]
        exact dt_tester_term_typeof_of_non_none hApplyNN
      have hxSmt :
          __smtx_typeof (__eo_to_smt x) = SmtType.Datatype s d :=
        dt_tester_arg_datatype_of_non_none hApplyNN
      have hCtorSmt :
          __smtx_typeof_dt_cons_rec (SmtType.Datatype s d)
              (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i ≠ SmtType.None :=
        dt_tester_ctor_type_non_none_of_non_none hApplyNN
      have hxTrans :
          __eo_to_smt_type (__eo_typeof x) = SmtType.Datatype s d :=
        eo_to_smt_type_typeof_of_smt_type_from_ih x ihX hxSmt (by simp)
      have hxNonStuck : __eo_typeof x ≠ Term.Stuck :=
        eo_term_ne_stuck_of_smt_type_non_none (__eo_typeof x) (by
          rw [hxTrans]
          simp)
      have hyNonStuck : __eo_typeof y ≠ Term.Stuck := by
        rcases eo_to_smt_eq_dt_cons_cases y s d i hCons with
          ⟨d0, hd, hyEq, hReserved⟩ | ⟨hs, hd, hi, hyEq⟩
        · subst y
          subst d
          let dd := __eo_to_smt_datatype_decl d0
          let body := __smtx_dt_resolve (__smtx_dd_lookup s dd) dd
          have hBaseWf : __smtx_type_wf (SmtType.Datatype s dd) = true :=
            Smtm.smt_datatype_wf_of_non_none_type (__eo_to_smt x) s dd
              (by simpa [dd] using hxSmt)
          have hRecWf : __smtx_type_wf_rec (SmtType.Datatype s dd) = true :=
            smtx_type_wf_rec_of_type_wf (by simp)
              (by intro A B h; cases h) (by intro A B h; cases h) hBaseWf
          have hTypeNoNone : noNoneTy (SmtType.Datatype s dd) = true :=
            noNoneTy_of_wf _ hRecWf
          have hLookupWf : __smtx_dt_wf_rec dd (__smtx_dd_lookup s dd) = true :=
            datatype_wf_rec_of_type_wf hBaseWf
          have hLookupNoNone : noNoneDt (__smtx_dd_lookup s dd) = true :=
            noNoneDt_of_wf dd (__smtx_dd_lookup s dd) hLookupWf
          have hDeclNoNone : noNoneDecl dd = true := by
            simpa [noNoneTy] using hTypeNoNone
          have hResolve :
              __eo_to_smt_datatype (__eo_dd_resolve s d0) = body :=
            eo_to_smt_dd_resolve_of_no_none s d0
              (by simpa [dd] using hLookupNoNone)
              (by simpa [dd] using hDeclNoNone)
          have hBodyNoNone : noNoneDt body = true :=
            noNoneDt_resolve (__smtx_dd_lookup s dd) dd hLookupNoNone hDeclNoNone
          have hEoBodyNoNone :
              noNoneDt (__eo_to_smt_datatype (__eo_dd_resolve s d0)) = true := by
            rw [hResolve]
            exact hBodyNoNone
          have hBaseEoNoNone :
              noNoneTy (__eo_to_smt_type (Term.DatatypeType s d0)) = true := by
            simpa [dd, __eo_to_smt_type, hReserved, native_ite] using hTypeNoNone
          have hRec := eo_to_smt_typeof_dt_cons_rec_of_no_none_apply
            (Term.DatatypeType s d0) (__eo_dd_resolve s d0) i
            (by simp) hBaseEoNoNone hEoBodyNoNone
          have hRawNN :
              __smtx_typeof_dt_cons_rec
                  (__eo_to_smt_type (Term.DatatypeType s d0))
                  (__eo_to_smt_datatype (__eo_dd_resolve s d0)) i ≠
                SmtType.None := by
            simpa [dd, body, __eo_to_smt_type, hReserved, native_ite,
              hResolve] using hCtorSmt
          change
            __eo_typeof_dt_cons_rec (Term.DatatypeType s d0)
                (__eo_dd_resolve s d0) i ≠ Term.Stuck
          exact eo_term_ne_stuck_of_smt_type_non_none _ (by
            rw [hRec.1]
            exact hRawNN)
        · subst y
          simp
      have hEo :
          __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.is y) x)) =
            SmtType.Bool := by
        change __eo_to_smt_type (__eo_typeof_is (__eo_typeof y) (__eo_typeof x)) =
          SmtType.Bool
        rw [eo_typeof_is_bool_of_non_stuck (__eo_typeof y) (__eo_typeof x)
          hyNonStuck hxNonStuck]
        rfl
      exact hSmt.trans hEo.symm
  | _ =>
      exact eo_to_smt_typeof_matches_translation_of_smt_none
        (Term.Apply (Term.UOp1 UserOp1.is y) x)
        (by
          change __smtx_typeof (SmtTerm.Apply (__eo_to_smt_tester (__eo_to_smt y)) (__eo_to_smt x)) =
            SmtType.None
          rw [hCons]
          simp [__eo_to_smt_tester, typeof_apply_none_eq])
        hNonNone

/-- Simplifies EO-to-SMT translation for unary `set_choose`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_set_choose
    (x : Term)
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_choose) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_choose) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.UOp UserOp.set_choose) x)) := by
  let T := __eo_to_smt_set_elem_type (__smtx_typeof (__eo_to_smt x))
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.UOp UserOp.set_choose) x) =
        SmtTerm.map_diff (__eo_to_smt x) (SmtTerm.set_empty T) := by
    rfl
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_choose) x)) =
        __eo_to_smt_type
          (__eo_typeof (Term.Apply (Term.UOp UserOp.set_choose) x)) := by
    rw [hTranslate]
    have hMapNN :
        term_has_non_none_type
          (SmtTerm.map_diff (__eo_to_smt x) (SmtTerm.set_empty T)) := by
      unfold term_has_non_none_type
      simpa [hTranslate] using hNonNone
    rcases map_diff_args_of_non_none hMapNN with hMap | hSet
    · rcases hMap with ⟨A, B, h1, h2, hRes⟩
      cases hWf : __smtx_type_wf (SmtType.Set T) <;>
        simp [__smtx_typeof, __smtx_typeof_guard_wf, native_ite, hWf] at h2
    · rcases hSet with ⟨A, h1, h2, hRes⟩
      rcases eo_typeof_eq_set_of_smt_set_from_ih x ihX h1 with
        ⟨U, hXU, hU⟩
      have hEo :
          __eo_to_smt_type
              (__eo_typeof (Term.Apply (Term.UOp UserOp.set_choose) x)) =
            A :=
        (eo_to_smt_type_typeof_apply_set_choose_of_set x U hXU).trans hU
      exact hRes.trans hEo.symm
  exact hSmt

/-- Top-level valid EO types are injective under translation, including `RegLan`. -/
private theorem eo_to_smt_type_eq_of_top_valid_apply_local
    {T U : Term}
    (hValid : eo_type_valid T)
    (hEq : __eo_to_smt_type T = __eo_to_smt_type U) :
    T = U := by
  exact eo_to_smt_type_eq_of_valid hValid hEq

private theorem eo_typeof_typed_list_nil_of_non_stuck_apply
    (T : Term) (hT : T ≠ Term.Stuck) :
    __eo_typeof__at__at_TypedList_nil Term.Type T =
      Term.Apply (Term.UOp UserOp._at__at_TypedList) T := by
  cases T <;> simp [__eo_typeof__at__at_TypedList_nil] at hT ⊢

private theorem eo_typeof_typed_list_cons_self_of_non_stuck_apply
    (T : Term) (hT : T ≠ Term.Stuck) :
    __eo_typeof__at__at_TypedList_cons T
        (Term.Apply (Term.UOp UserOp._at__at_TypedList) T) =
      Term.Apply (Term.UOp UserOp._at__at_TypedList) T := by
  cases T <;> simp [__eo_typeof__at__at_TypedList_cons, __eo_requires,
    __eo_eq, native_ite, native_teq, native_not] at hT ⊢

private theorem eo_to_smt_typed_list_elem_type_of_non_none_apply
    (root : Term)
    (ih :
      ∀ term,
        sizeOf term < sizeOf root ->
        __smtx_typeof (__eo_to_smt term) ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt term) = __eo_to_smt_type (__eo_typeof term) ∧
          eo_type_valid (__eo_typeof term)) :
    ∀ xs,
      sizeOf xs < sizeOf root ->
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ->
        ∃ T,
          __eo_typeof xs = Term.Apply (Term.UOp UserOp._at__at_TypedList) T ∧
            __eo_to_smt_type T = __eo_to_smt_typed_list_elem_type xs ∧
            eo_type_valid T
  | Term.Apply f xs, hLt, hNonNone => by
      cases f with
      | UOp op =>
          cases op with
          | _at__at_TypedList_nil =>
              have hWf : __smtx_type_wf (__eo_to_smt_type xs) = true := by
                by_cases hWf : __smtx_type_wf (__eo_to_smt_type xs) = true
                · exact hWf
                · exfalso
                  exact hNonNone (by
                    simp [__eo_to_smt_typed_list_elem_type, native_ite, hWf])
              have hTType : __eo_typeof xs = Term.Type :=
                eo_typeof_type_of_smt_type_wf xs hWf
              have hTValid : eo_type_valid xs :=
                eo_type_valid_of_smt_wf xs hWf
              refine ⟨xs, ?_, ?_, hTValid⟩
              · change
                  __eo_typeof__at__at_TypedList_nil (__eo_typeof xs) xs =
                    Term.Apply (Term.UOp UserOp._at__at_TypedList) xs
                rw [hTType]
                exact eo_typeof_typed_list_nil_of_non_stuck_apply xs
                  (eo_type_valid_not_stuck hTValid)
              · simp [__eo_to_smt_typed_list_elem_type, native_ite, hWf]
          | _ =>
              exfalso
              exact hNonNone (by simp [__eo_to_smt_typed_list_elem_type])
      | Apply g t =>
          cases g with
          | UOp op =>
              cases op with
              | _at__at_TypedList_cons =>
                  let headTy := __smtx_typeof (__eo_to_smt t)
                  let tailTy := __eo_to_smt_typed_list_elem_type xs
                  have hGuard : native_Teq headTy tailTy = true := by
                    by_cases hGuard : native_Teq headTy tailTy = true
                    · exact hGuard
                    · exfalso
                      exact hNonNone (by
                        simp [__eo_to_smt_typed_list_elem_type, headTy, tailTy,
                          native_ite, hGuard])
                  have hHeadNN : headTy ≠ SmtType.None := by
                    change
                      (native_ite (native_Teq headTy tailTy) headTy SmtType.None) ≠
                        SmtType.None at hNonNone
                    rw [hGuard] at hNonNone
                    exact hNonNone
                  have hTailNN : tailTy ≠ SmtType.None := by
                    intro hTailNone
                    cases hHead : headTy <;>
                      simp [headTy, tailTy, hHead, hTailNone, native_Teq] at hGuard hHeadNN
                  have hHeadLt : sizeOf t < sizeOf root := by
                    simp at hLt
                    omega
                  have hTailLt : sizeOf xs < sizeOf root := by
                    simp at hLt
                    omega
                  rcases eo_to_smt_typed_list_elem_type_of_non_none_apply root ih
                      xs hTailLt hTailNN with
                    ⟨T, hTsType, hTsSmt, hTValid⟩
                  have hHeadTypeEq :
                      __eo_typeof t = T := by
                    have hHeadEqTail : headTy = tailTy := by
                      simpa [native_Teq] using hGuard
                    have hHeadSmt :
                        __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type T := by
                      calc
                        __smtx_typeof (__eo_to_smt t) = headTy := rfl
                        _ = tailTy := hHeadEqTail
                        _ = __eo_to_smt_type T := hTsSmt.symm
                    have hHeadIH := ih t hHeadLt (by simpa [headTy] using hHeadNN)
                    exact eo_to_smt_type_eq_of_top_valid_apply_local hHeadIH.2
                      (by rw [← hHeadIH.1, hHeadSmt])
                  refine ⟨T, ?_, ?_, hTValid⟩
                  · change
                      __eo_typeof__at__at_TypedList_cons (__eo_typeof t)
                          (__eo_typeof xs) =
                        Term.Apply (Term.UOp UserOp._at__at_TypedList) T
                    rw [hTsType, hHeadTypeEq]
                    exact eo_typeof_typed_list_cons_self_of_non_stuck_apply T
                      (eo_type_valid_not_stuck hTValid)
                  · have hHeadEqTail : headTy = tailTy := by
                      simpa [native_Teq] using hGuard
                    have hElemCons :
                        __eo_to_smt_typed_list_elem_type
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) t)
                              xs) =
                          headTy := by
                      dsimp [__eo_to_smt_typed_list_elem_type, headTy, tailTy]
                      rw [hGuard]
                      simp [native_ite]
                    calc
                      __eo_to_smt_type T = tailTy := hTsSmt
                      _ = headTy := hHeadEqTail.symm
                      _ =
                          __eo_to_smt_typed_list_elem_type
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) t)
                              xs) :=
                        hElemCons.symm
              | _ =>
                  exfalso
                  exact hNonNone (by simp [__eo_to_smt_typed_list_elem_type])
          | _ =>
              exfalso
              exact hNonNone (by simp [__eo_to_smt_typed_list_elem_type])
      | _ =>
          exfalso
          exact hNonNone (by simp [__eo_to_smt_typed_list_elem_type])
  | Term.UOp op, hLt, hNonNone => by
      exact False.elim (hNonNone (by simp [__eo_to_smt_typed_list_elem_type]))
  | Term.UOp1 op x, hLt, hNonNone => by
      exact False.elim (hNonNone (by simp [__eo_to_smt_typed_list_elem_type]))
  | Term.UOp2 op x y, hLt, hNonNone => by
      exact False.elim (hNonNone (by simp [__eo_to_smt_typed_list_elem_type]))
  | Term.UOp3 op x y z, hLt, hNonNone => by
      exact False.elim (hNonNone (by simp [__eo_to_smt_typed_list_elem_type]))
  | Term.__eo_List, hLt, hNonNone => by
      exact False.elim (hNonNone (by simp [__eo_to_smt_typed_list_elem_type]))
  | Term.__eo_List_nil, hLt, hNonNone => by
      exact False.elim (hNonNone (by simp [__eo_to_smt_typed_list_elem_type]))
  | Term.__eo_List_cons, hLt, hNonNone => by
      exact False.elim (hNonNone (by simp [__eo_to_smt_typed_list_elem_type]))
  | Term.Bool, hLt, hNonNone => by
      exact False.elim (hNonNone (by simp [__eo_to_smt_typed_list_elem_type]))
  | Term.Boolean b, hLt, hNonNone => by
      exact False.elim (hNonNone (by simp [__eo_to_smt_typed_list_elem_type]))
  | Term.Numeral n, hLt, hNonNone => by
      exact False.elim (hNonNone (by simp [__eo_to_smt_typed_list_elem_type]))
  | Term.Rational r, hLt, hNonNone => by
      exact False.elim (hNonNone (by simp [__eo_to_smt_typed_list_elem_type]))
  | Term.String s, hLt, hNonNone => by
      exact False.elim (hNonNone (by simp [__eo_to_smt_typed_list_elem_type]))
  | Term.Binary w n, hLt, hNonNone => by
      exact False.elim (hNonNone (by simp [__eo_to_smt_typed_list_elem_type]))
  | Term.Type, hLt, hNonNone => by
      exact False.elim (hNonNone (by simp [__eo_to_smt_typed_list_elem_type]))
  | Term.Stuck, hLt, hNonNone => by
      exact False.elim (hNonNone (by simp [__eo_to_smt_typed_list_elem_type]))
  | Term.FunType, hLt, hNonNone => by
      exact False.elim (hNonNone (by simp [__eo_to_smt_typed_list_elem_type]))
  | Term.Var name T, hLt, hNonNone => by
      exact False.elim (hNonNone (by simp [__eo_to_smt_typed_list_elem_type]))
  | Term.DatatypeType s d, hLt, hNonNone => by
      exact False.elim (hNonNone (by simp [__eo_to_smt_typed_list_elem_type]))
  | Term.DatatypeTypeRef s, hLt, hNonNone => by
      exact False.elim (hNonNone (by simp [__eo_to_smt_typed_list_elem_type]))
  | Term.DtcAppType T U, hLt, hNonNone => by
      exact False.elim (hNonNone (by simp [__eo_to_smt_typed_list_elem_type]))
  | Term.DtCons s d i, hLt, hNonNone => by
      exact False.elim (hNonNone (by simp [__eo_to_smt_typed_list_elem_type]))
  | Term.DtSel s d i j, hLt, hNonNone => by
      exact False.elim (hNonNone (by simp [__eo_to_smt_typed_list_elem_type]))
  | Term.USort i, hLt, hNonNone => by
      exact False.elim (hNonNone (by simp [__eo_to_smt_typed_list_elem_type]))
  | Term.UConst i T, hLt, hNonNone => by
      exact False.elim (hNonNone (by simp [__eo_to_smt_typed_list_elem_type]))
termination_by xs hLt hNonNone => sizeOf xs
decreasing_by
  all_goals simp_wf
  all_goals omega

private theorem eo_to_smt_set_insert_shape_of_non_none :
    ∀ xs base,
      __smtx_typeof (__eo_to_smt_set_insert xs base) ≠ SmtType.None ->
        ∃ A,
          __smtx_typeof (__eo_to_smt_set_insert xs base) = SmtType.Set A ∧
          __smtx_typeof base = SmtType.Set A ∧
          __eo_to_smt_typed_list_elem_type xs = A ∧
          A ≠ SmtType.None := by
  intro xs base hNonNone
  cases xs
  all_goals
    try
      exfalso
      apply hNonNone
      simp [__eo_to_smt_set_insert, smtx_typeof_none]
  case Apply f tail =>
    cases f
    all_goals
      try
        exfalso
        apply hNonNone
        simp [__eo_to_smt_set_insert, smtx_typeof_none]
    case UOp op =>
      cases op
      case _at__at_TypedList_nil =>
        cases hGuard :
            native_Teq (__smtx_typeof base)
              (SmtType.Set (__eo_to_smt_type tail))
        · exfalso
          apply hNonNone
          simp [__eo_to_smt_set_insert, hGuard, native_ite, smtx_typeof_none]
        · have hBase :
              __smtx_typeof base = SmtType.Set (__eo_to_smt_type tail) := by
            simpa [native_Teq] using hGuard
          have hBaseNN : term_has_non_none_type base := by
            unfold term_has_non_none_type
            rw [hBase]
            simp
          have hSetWf :
              __smtx_type_wf (SmtType.Set (__eo_to_smt_type tail)) = true :=
            smt_term_set_type_wf_of_non_none base hBaseNN hBase
          have hTailWf : __smtx_type_wf (__eo_to_smt_type tail) = true :=
            set_type_wf_component_of_wf hSetWf
          have hTailNN : __eo_to_smt_type tail ≠ SmtType.None :=
            type_wf_non_none hTailWf
          refine ⟨__eo_to_smt_type tail, ?_, hBase, ?_, hTailNN⟩
          · simpa [__eo_to_smt_set_insert, hGuard, native_ite] using hBase
          · simp [__eo_to_smt_typed_list_elem_type, native_ite, hTailWf]
      all_goals
        exfalso
        apply hNonNone
        simp [__eo_to_smt_set_insert, smtx_typeof_none]
    case Apply f' head =>
      cases f'
      all_goals
        try
          exfalso
          apply hNonNone
          simp [__eo_to_smt_set_insert, smtx_typeof_none]
      case UOp op =>
        cases op
        case _at__at_TypedList_cons =>
          have hNNUnion : term_has_non_none_type
              (SmtTerm.set_union (SmtTerm.set_singleton (__eo_to_smt head))
                (__eo_to_smt_set_insert tail base)) := by
            unfold term_has_non_none_type
            change
              __smtx_typeof
                  (__eo_to_smt_set_insert
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) head)
                      tail) base) ≠ SmtType.None at hNonNone
            simpa [__eo_to_smt_set_insert] using hNonNone
          rcases set_binop_args_of_non_none (op := SmtTerm.set_union)
              (typeof_set_union_eq
                (SmtTerm.set_singleton (__eo_to_smt head))
                (__eo_to_smt_set_insert tail base))
              hNNUnion with
            ⟨A, hHeadSet, hTailSet⟩
          have hTailNN :
              __smtx_typeof (__eo_to_smt_set_insert tail base) ≠ SmtType.None := by
            rw [hTailSet]
            simp
          rcases eo_to_smt_set_insert_shape_of_non_none tail base hTailNN with
            ⟨B, hTailSmt, hBase, hTailElem, hBNN⟩
          have hAB : A = B := by
            have hSetEq : SmtType.Set A = SmtType.Set B :=
              hTailSet.symm.trans hTailSmt
            cases hSetEq
            rfl
          have hBaseA : __smtx_typeof base = SmtType.Set A := by
            rw [hAB]
            exact hBase
          have hTailElemA : __eo_to_smt_typed_list_elem_type tail = A :=
            hTailElem.trans hAB.symm
          have hHeadArg := set_singleton_type_eq_arg_of_eq hHeadSet
          have hSmt :
              __smtx_typeof
                  (__eo_to_smt_set_insert
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) head)
                      tail) base) = SmtType.Set A := by
            change
              __smtx_typeof
                  (SmtTerm.set_union (SmtTerm.set_singleton (__eo_to_smt head))
                    (__eo_to_smt_set_insert tail base)) = SmtType.Set A
            rw [typeof_set_union_eq, hHeadSet, hTailSet]
            simp [__smtx_typeof_sets_op_2, native_ite, native_Teq]
          have hElem :
              __eo_to_smt_typed_list_elem_type
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) head)
                    tail) = A := by
            change
              native_ite
                (native_Teq (__smtx_typeof (__eo_to_smt head))
                  (__eo_to_smt_typed_list_elem_type tail))
                (__smtx_typeof (__eo_to_smt head)) SmtType.None = A
            rw [hHeadArg.1, hTailElemA]
            simp [native_Teq, native_ite]
          exact ⟨A, hSmt, hBaseA, hElem, hHeadArg.2⟩
        all_goals
          exfalso
          apply hNonNone
          simp [__eo_to_smt_set_insert, smtx_typeof_none]
termination_by xs base _ => sizeOf xs

/-- Shape information for a non-`None` top-level `set_insert` translation. -/
private theorem set_insert_top_translation_shape
    (x y : Term)
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (ihBelowAll :
      ∀ term,
        sizeOf term <
          sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) y) x) ->
        __smtx_typeof (__eo_to_smt term) ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt term) = __eo_to_smt_type (__eo_typeof term) ∧
          eo_type_valid (__eo_typeof term))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) y) x)) ≠
        SmtType.None) :
    ∃ A U,
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) y) x)) =
        SmtType.Set A ∧
      __eo_typeof y = Term.Apply (Term.UOp UserOp._at__at_TypedList) U ∧
      __eo_typeof x = Term.Apply (Term.UOp UserOp.Set) U ∧
      __eo_to_smt_type U = A ∧
      A ≠ SmtType.None := by
  rcases eo_to_smt_set_insert_shape_of_non_none y (__eo_to_smt x) hNonNone with
    ⟨A, hSmt, hBaseSmt, hElem, hANN⟩
  rcases eo_typeof_eq_set_of_smt_set_from_ih x ihX hBaseSmt with
    ⟨U, hBase, hU⟩
  have hElemNN : __eo_to_smt_typed_list_elem_type y ≠ SmtType.None := by
    rw [hElem]
    exact hANN
  rcases eo_to_smt_typed_list_elem_type_of_non_none_apply
      (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) y) x)
      ihBelowAll y (by simp; omega) hElemNN with
    ⟨V, hList, hV, hVValid⟩
  have hVU : V = U :=
    eo_to_smt_type_eq_of_top_valid_apply_local hVValid (by rw [hV, hElem, hU])
  subst V
  exact ⟨A, U, hSmt, hList, hBase, hU, hANN⟩

/-- Simplifies EO-to-SMT translation for `set_insert`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_set_insert
    (x y : Term)
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (ihBelowAll :
      ∀ term,
        sizeOf term <
          sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) y) x) ->
        __smtx_typeof (__eo_to_smt term) ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt term) = __eo_to_smt_type (__eo_typeof term) ∧
          eo_type_valid (__eo_typeof term))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) y) x)) ≠
        SmtType.None) :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) y) x)) := by
  rcases set_insert_top_translation_shape x y ihX ihBelowAll hNonNone with
    ⟨A, U, hSmt, hList, hBase, hU, hANN⟩
  have hUNN : __eo_to_smt_type U ≠ SmtType.None := by
    rw [hU]
    exact hANN
  have hUNS : U ≠ Term.Stuck :=
    eo_term_ne_stuck_of_smt_type_non_none U hUNN
  have hEo :
      __eo_to_smt_type
          (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) y) x)) =
        SmtType.Set A := by
    change __eo_to_smt_type (__eo_typeof_set_insert (__eo_typeof y) (__eo_typeof x)) =
      SmtType.Set A
    rw [hList, hBase]
    simpa [__eo_typeof_set_insert, __eo_to_smt_type, hU,
      smtx_typeof_guard_of_non_none A (SmtType.Set A) hANN] using
      congrArg __eo_to_smt_type
        (eo_requires_eo_eq_self_of_non_stuck U (Term.Apply (Term.UOp UserOp.Set) U) hUNS)
  exact hSmt.trans hEo.symm

/-- Simplifies EO-to-SMT translation for set binary operators returning a set. -/
private theorem eo_to_smt_typeof_matches_translation_apply_set_binop
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (x y : Term)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x) =
        smtOp (__eo_to_smt y) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_sets_op_2
          (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x)))
    (hEoType :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x) =
        __eo_typeof_set_union (__eo_typeof y) (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) := by
  have hApplyNN :
      term_has_non_none_type (smtOp (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases set_binop_args_of_non_none (op := smtOp) hTy hApplyNN with
    ⟨A, hY, hX⟩
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
        SmtType.Set A := by
    rw [hTranslate, hTy]
    simp [__smtx_typeof_sets_op_2, native_ite, native_Teq, hY, hX]
  have hAWF :
      smtx_type_field_wf_rec A native_reflist_nil :=
    smtx_set_component_field_wf_rec_of_non_none_type_apply (__eo_to_smt y) A hY
  have hANN : A ≠ SmtType.None :=
    smtx_type_field_wf_rec_ne_none hAWF
  rcases eo_typeof_eq_set_of_smt_set_from_ih y ihY hY with ⟨U, hYU, hU⟩
  rcases eo_typeof_eq_set_of_smt_set_from_ih x ihX hX with ⟨V, hXV, hV⟩
  have hVU : V = U :=
    eo_to_smt_type_injective_of_field_wf_rec hV hU hAWF
  have hXU : __eo_typeof x = Term.Apply (Term.UOp UserOp.Set) U := by
    rw [hXV, hVU]
  have hUNN : __eo_to_smt_type U ≠ SmtType.None := by
    rw [hU]
    exact hANN
  have hUNS : U ≠ Term.Stuck :=
    eo_term_ne_stuck_of_smt_type_non_none U hUNN
  have hEo :
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
        SmtType.Set A := by
    rw [hEoType, hYU, hXU]
    simpa [__eo_typeof_set_union, __eo_to_smt_type, hU,
      smtx_typeof_guard_of_non_none A (SmtType.Set A) hANN] using
      congrArg __eo_to_smt_type
        (eo_requires_eo_eq_self_of_non_stuck U (Term.Apply (Term.UOp UserOp.Set) U) hUNS)
  exact hSmt.trans hEo.symm

/-- Simplifies EO-to-SMT translation for set binary predicates. -/
private theorem eo_to_smt_typeof_matches_translation_apply_set_pred_binop
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (x y : Term)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x) =
        smtOp (__eo_to_smt y) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_sets_op_2_ret
          (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x)) SmtType.Bool)
    (hEoType :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x) =
        __eo_typeof_set_subset (__eo_typeof y) (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) := by
  have hApplyNN :
      term_has_non_none_type (smtOp (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases set_binop_ret_args_of_non_none (op := smtOp) hTy hApplyNN with
    ⟨A, hY, hX⟩
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
        SmtType.Bool := by
    rw [hTranslate, hTy]
    simp [__smtx_typeof_sets_op_2_ret, native_ite, native_Teq, hY, hX]
  have hAWF :
      smtx_type_field_wf_rec A native_reflist_nil :=
    smtx_set_component_field_wf_rec_of_non_none_type_apply (__eo_to_smt y) A hY
  have hANN : A ≠ SmtType.None :=
    smtx_type_field_wf_rec_ne_none hAWF
  rcases eo_typeof_eq_set_of_smt_set_from_ih y ihY hY with ⟨U, hYU, hU⟩
  rcases eo_typeof_eq_set_of_smt_set_from_ih x ihX hX with ⟨V, hXV, hV⟩
  have hVU : V = U :=
    eo_to_smt_type_injective_of_field_wf_rec hV hU hAWF
  have hXU : __eo_typeof x = Term.Apply (Term.UOp UserOp.Set) U := by
    rw [hXV, hVU]
  have hUNN : __eo_to_smt_type U ≠ SmtType.None := by
    rw [hU]
    exact hANN
  have hUNS : U ≠ Term.Stuck :=
    eo_term_ne_stuck_of_smt_type_non_none U hUNN
  have hEo :
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
        SmtType.Bool := by
    rw [hEoType, hYU, hXU]
    simpa [__eo_typeof_set_subset] using
      congrArg __eo_to_smt_type
        (eo_requires_eo_eq_self_of_non_stuck U Term.Bool hUNS)
  exact hSmt.trans hEo.symm

/-- Simplifies EO-to-SMT translation for Boolean binary operators. -/
private theorem eo_to_smt_typeof_matches_translation_apply_bool_binop
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (x y : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x) =
        smtOp (__eo_to_smt y) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt y) (__eo_to_smt x)) =
        native_ite (native_Teq (__smtx_typeof (__eo_to_smt y)) SmtType.Bool)
          (native_ite (native_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Bool)
            SmtType.Bool SmtType.None)
          SmtType.None)
    (hEo :
      __smtx_typeof (__eo_to_smt y) = SmtType.Bool ->
      __smtx_typeof (__eo_to_smt x) = SmtType.Bool ->
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
        SmtType.Bool)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) := by
  have hApplyNN :
      term_has_non_none_type (smtOp (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  have hArgs := bool_binop_args_bool_of_non_none (op := smtOp) hTy hApplyNN
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
        SmtType.Bool := by
    rw [hTranslate, hTy]
    simp [hArgs.1, hArgs.2, native_ite, native_Teq]
  exact hSmt.trans (hEo hArgs.1 hArgs.2).symm

/-- Simplifies EO-to-SMT translation for arithmetic binary operators returning their input type. -/
private theorem eo_to_smt_typeof_matches_translation_apply_arith_binop
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (x y : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x) =
        smtOp (__eo_to_smt y) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_arith_overload_op_2
          (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x)))
    (hEo :
      ∀ T : SmtType,
        __smtx_typeof (__eo_to_smt y) = T ->
        __smtx_typeof (__eo_to_smt x) = T ->
        (T = SmtType.Int ∨ T = SmtType.Real) ->
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) = T)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) := by
  have hApplyNN :
      term_has_non_none_type (smtOp (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases arith_binop_args_of_non_none (op := smtOp) hTy hApplyNN with hArgs | hArgs
  · have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
          SmtType.Int := by
      rw [hTranslate, hTy]
      simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
    exact hSmt.trans (hEo SmtType.Int hArgs.1 hArgs.2 (Or.inl rfl)).symm
  · have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
          SmtType.Real := by
      rw [hTranslate, hTy]
      simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
    exact hSmt.trans (hEo SmtType.Real hArgs.1 hArgs.2 (Or.inr rfl)).symm

/-- Simplifies EO-to-SMT translation for arithmetic comparisons returning Boolean. -/
private theorem eo_to_smt_typeof_matches_translation_apply_arith_bool_binop
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (x y : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x) =
        smtOp (__eo_to_smt y) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_arith_overload_op_2_ret
          (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x)) SmtType.Bool)
    (hEo :
      ∀ T : SmtType,
        __smtx_typeof (__eo_to_smt y) = T ->
        __smtx_typeof (__eo_to_smt x) = T ->
        (T = SmtType.Int ∨ T = SmtType.Real) ->
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
          SmtType.Bool)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) := by
  have hApplyNN :
      term_has_non_none_type (smtOp (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases arith_binop_ret_bool_args_of_non_none (op := smtOp) hTy hApplyNN with hArgs | hArgs
  · have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
          SmtType.Bool := by
      rw [hTranslate, hTy]
      simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
    exact hSmt.trans (hEo SmtType.Int hArgs.1 hArgs.2 (Or.inl rfl)).symm
  · have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
          SmtType.Bool := by
      rw [hTranslate, hTy]
      simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
    exact hSmt.trans (hEo SmtType.Real hArgs.1 hArgs.2 (Or.inr rfl)).symm

/-- Simplifies EO-to-SMT translation for arithmetic binary operators returning a fixed type. -/
private theorem eo_to_smt_typeof_matches_translation_apply_arith_ret_binop
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (ret : SmtType) (x y : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x) =
        smtOp (__eo_to_smt y) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_arith_overload_op_2_ret
          (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x)) ret)
    (hEo :
      ∀ T : SmtType,
        __smtx_typeof (__eo_to_smt y) = T ->
        __smtx_typeof (__eo_to_smt x) = T ->
        (T = SmtType.Int ∨ T = SmtType.Real) ->
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
          ret)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) := by
  have hApplyNN :
      term_has_non_none_type (smtOp (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases arith_binop_ret_args_of_non_none (op := smtOp) hTy hApplyNN with hArgs | hArgs
  · have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
          ret := by
      rw [hTranslate, hTy]
      simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
    exact hSmt.trans (hEo SmtType.Int hArgs.1 hArgs.2 (Or.inl rfl)).symm
  · have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
          ret := by
      rw [hTranslate, hTy]
      simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
    exact hSmt.trans (hEo SmtType.Real hArgs.1 hArgs.2 (Or.inr rfl)).symm

/-- Simplifies EO-to-SMT translation for integer-only binary operators. -/
private theorem eo_to_smt_typeof_matches_translation_apply_int_binop
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (ret : SmtType) (x y : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x) =
        smtOp (__eo_to_smt y) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt y) (__eo_to_smt x)) =
        native_ite (native_Teq (__smtx_typeof (__eo_to_smt y)) SmtType.Int)
          (native_ite (native_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Int)
            ret SmtType.None)
          SmtType.None)
    (hEo :
      __smtx_typeof (__eo_to_smt y) = SmtType.Int ->
      __smtx_typeof (__eo_to_smt x) = SmtType.Int ->
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
        ret)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) := by
  have hApplyNN :
      term_has_non_none_type (smtOp (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  have hArgs := int_binop_args_of_non_none (op := smtOp) (R := ret) hTy hApplyNN
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
        ret := by
    rw [hTranslate, hTy]
    simp [hArgs.1, hArgs.2, native_ite, native_Teq]
  exact hSmt.trans (hEo hArgs.1 hArgs.2).symm

/-- Purified selector heads keep the selector result EO type. -/
theorem eo_to_smt_eq_dt_sel_cases
    (y : Term) (s : native_String) (d : SmtDatatypeDecl) (i j : native_Nat)
    (hy : __eo_to_smt y = SmtTerm.DtSel s d i j) :
    (∃ d0, d = __eo_to_smt_datatype_decl d0 ∧ y = Term.DtSel s d0 i j ∧
      __eo_reserved_datatype_name s = false) ∨
      (∃ z, y = Term._at_purify z ∧ __eo_to_smt z = SmtTerm.DtSel s d i j) := by
  cases y
  case DtSel s0 d0 i0 j0 =>
    cases hReserved : __eo_reserved_datatype_name s0
    · simp [eo_to_smt_term_dt_sel, native_ite, hReserved] at hy
      rcases hy with ⟨hs, hd, hi, hj⟩
      cases hs
      cases hd
      cases hi
      cases hj
      exact Or.inl ⟨d0, rfl, rfl, hReserved⟩
    · simp [eo_to_smt_term_dt_sel, native_ite, hReserved] at hy
  case DtCons s0 d0 i0 =>
    exfalso
    cases hReserved : __eo_reserved_datatype_name s0 <;>
      simp [eo_to_smt_term_dt_cons, native_ite, hReserved] at hy
  case UOp1 op z =>
    cases op <;> try (exfalso; cases hy)
    case seq_empty =>
      exfalso
      change __eo_to_smt_seq_empty (__eo_to_smt_type z) = SmtTerm.DtSel s d i j at hy
      cases hTy : __eo_to_smt_type z <;> simp [__eo_to_smt_seq_empty, hTy] at hy
    case set_empty =>
      exfalso
      change __eo_to_smt_set_empty (__eo_to_smt_type z) = SmtTerm.DtSel s d i j at hy
      cases hTy : __eo_to_smt_type z <;> simp [__eo_to_smt_set_empty, hTy] at hy
  case Apply f x =>
    exact (eo_to_smt_apply_ne_dt_sel f x s d i j hy).elim
  case UOp op =>
    exfalso
    cases op <;> cases hy
  case Var name T =>
    exfalso
    cases name <;> cases hy
  case UOp2 op q idx =>
    cases op <;> try (exfalso; cases hy)
    case _at_quantifiers_skolemize =>
      exact (eo_to_smt_quant_skolemize_top_ne_dt_sel q idx s d i j hy).elim
    case _at_const =>
      exact (eo_to_smt_at_const_ne_dt_sel q idx s d i j hy).elim
  case UOp3 op t r idx =>
    cases op
    case _at_re_unfold_pos_component =>
      exfalso
      change native_ite (__eo_to_smt_nat_is_valid idx)
          (__eo_to_smt_re_unfold_pos_component (__eo_to_smt t) (__eo_to_smt r)
            (__eo_to_smt_nat idx))
          SmtTerm.None =
        SmtTerm.DtSel s d i j at hy
      unfold native_ite at hy
      split at hy <;> try cases hy
      exact eo_to_smt_re_unfold_ne_dt_sel _ _ _ _ _ _ _ hy
    case _at_witness_string_length =>
      exfalso
      change native_ite (__eo_to_smt_nat_is_valid r)
          (native_ite (__eo_to_smt_nat_is_valid idx)
            (SmtTerm.choice (native_string_lit "@x") (__eo_to_smt_type t)
              (SmtTerm.eq
                (SmtTerm.str_len (SmtTerm.Var (native_string_lit "@x") (__eo_to_smt_type t)))
                (__eo_to_smt r))) SmtTerm.None) SmtTerm.None =
        SmtTerm.DtSel s d i j at hy
      unfold native_ite at hy
      split at hy <;> try cases hy
      split at hy <;> cases hy
  all_goals
    exfalso
    cases hy

/-- EO translation never produces a bare datatype tester. -/
theorem eo_to_smt_ne_dt_tester
    (y : Term) (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    __eo_to_smt y ≠ SmtTerm.DtTester s d i := by
  intro hy
  cases y
  case UOp1 op z =>
    cases op <;> try (exfalso; cases hy)
    case seq_empty =>
      exfalso
      change __eo_to_smt_seq_empty (__eo_to_smt_type z) = SmtTerm.DtTester s d i at hy
      cases hTy : __eo_to_smt_type z <;> simp [__eo_to_smt_seq_empty, hTy] at hy
    case set_empty =>
      exfalso
      change __eo_to_smt_set_empty (__eo_to_smt_type z) = SmtTerm.DtTester s d i at hy
      cases hTy : __eo_to_smt_type z <;> simp [__eo_to_smt_set_empty, hTy] at hy
  case Apply f x =>
    exact (eo_to_smt_apply_ne_dt_tester f x s d i hy).elim
  case DtCons s0 d0 i0 =>
    exfalso
    cases hReserved : __eo_reserved_datatype_name s0 <;>
      simp [eo_to_smt_term_dt_cons, native_ite, hReserved] at hy
  case DtSel s0 d0 i0 j0 =>
    exfalso
    cases hReserved : __eo_reserved_datatype_name s0 <;>
      simp [eo_to_smt_term_dt_sel, native_ite, hReserved] at hy
  case UOp op =>
    exfalso
    cases op <;> cases hy
  case Var name T =>
    exfalso
    cases name <;> cases hy
  case UOp2 op q idx =>
    cases op <;> try (exfalso; cases hy)
    case _at_quantifiers_skolemize =>
      exact (eo_to_smt_quant_skolemize_top_ne_dt_tester q idx s d i hy).elim
    case _at_const =>
      exact (eo_to_smt_at_const_ne_dt_tester q idx s d i hy).elim
  case UOp3 op t r idx =>
    cases op
    case _at_re_unfold_pos_component =>
      exfalso
      change native_ite (__eo_to_smt_nat_is_valid idx)
          (__eo_to_smt_re_unfold_pos_component (__eo_to_smt t) (__eo_to_smt r)
            (__eo_to_smt_nat idx))
          SmtTerm.None =
        SmtTerm.DtTester s d i at hy
      unfold native_ite at hy
      split at hy <;> try cases hy
      exact eo_to_smt_re_unfold_ne_dt_tester _ _ _ _ _ _ hy
    case _at_witness_string_length =>
      exfalso
      change native_ite (__eo_to_smt_nat_is_valid r)
          (native_ite (__eo_to_smt_nat_is_valid idx)
            (SmtTerm.choice (native_string_lit "@x") (__eo_to_smt_type t)
              (SmtTerm.eq
                (SmtTerm.str_len (SmtTerm.Var (native_string_lit "@x") (__eo_to_smt_type t)))
                (__eo_to_smt r))) SmtTerm.None) SmtTerm.None =
        SmtTerm.DtTester s d i at hy
      unfold native_ite at hy
      split at hy <;> try cases hy
      split at hy <;> cases hy
  all_goals
    exfalso
    cases hy

/-- Purified selector heads keep the selector result EO type. -/
private theorem eo_to_smt_type_typeof_apply_purify_of_dt_sel_translation
    (x y : Term) (s : native_String) (d : SmtDatatypeDecl) (i j : native_Nat)
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hy : __eo_to_smt y = SmtTerm.DtSel s d i j)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Datatype s d)
    (hApplyNN : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtSel s d i j) (__eo_to_smt x))) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term._at_purify y) x)) =
      __smtx_ret_typeof_sel s d i j := by
  rcases eo_to_smt_eq_dt_sel_cases y s d i j hy with hSel | hPurify
  · rcases hSel with ⟨d0, hd, rfl, hReserved⟩
    have hx' : __smtx_typeof (__eo_to_smt x) = SmtType.Datatype s (__eo_to_smt_datatype_decl d0) := by
      simpa [hd] using hx
    have hApplyNN' :
        term_has_non_none_type
          (SmtTerm.Apply (SmtTerm.DtSel s (__eo_to_smt_datatype_decl d0) i j) (__eo_to_smt x)) := by
      simpa [hd] using hApplyNN
    have hHeadEq :
        __eo_typeof (Term._at_purify (Term.DtSel s d0 i j)) =
          __eo_typeof (Term.DtSel s d0 i j) := by
      rfl
    have hApplyEq :
        __eo_typeof (Term.Apply (Term._at_purify (Term.DtSel s d0 i j)) x) =
          __eo_typeof (Term.Apply (Term.DtSel s d0 i j) x) := by
      change
        __eo_typeof_apply (__eo_typeof (Term._at_purify (Term.DtSel s d0 i j))) (__eo_typeof x) =
          __eo_typeof_apply (__eo_typeof (Term.DtSel s d0 i j)) (__eo_typeof x)
      rw [hHeadEq]
    rw [hApplyEq]
    simpa [hd] using
      (eo_to_smt_type_typeof_apply_dt_sel_of_smt_datatype_from_ih
        x s d0 i j ihX hReserved hx' hApplyNN')
  · rcases hPurify with ⟨z, rfl, hz⟩
    have hHeadEq :
        __eo_typeof (Term._at_purify (Term._at_purify z)) =
          __eo_typeof (Term._at_purify z) := by
      change
        __eo_typeof__at_purify (__eo_typeof (Term._at_purify z)) =
          __eo_typeof (Term._at_purify z)
      cases hTy : __eo_typeof (Term._at_purify z) <;> rfl
    have hApplyEq :
        __eo_typeof (Term.Apply (Term._at_purify (Term._at_purify z)) x) =
          __eo_typeof (Term.Apply (Term._at_purify z) x) := by
      change
        __eo_typeof_apply (__eo_typeof (Term._at_purify (Term._at_purify z))) (__eo_typeof x) =
          __eo_typeof_apply (__eo_typeof (Term._at_purify z)) (__eo_typeof x)
      rw [hHeadEq]
    rw [hApplyEq]
    exact eo_to_smt_type_typeof_apply_purify_of_dt_sel_translation x z s d i j ihX hz hx hApplyNN

/-- A non-`None` regex-unfold component always returns a string. -/
private theorem smtx_typeof_re_unfold_pos_component_of_non_none
    (s r : SmtTerm)
    (n : native_Nat)
    (hNN : __smtx_typeof (__eo_to_smt_re_unfold_pos_component s r n) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt_re_unfold_pos_component s r n) = SmtType.Seq SmtType.Char := by
  induction n generalizing s r with
  | zero =>
      cases r <;> simp [__eo_to_smt_re_unfold_pos_component] at hNN ⊢
      case re_concat r1 r2 =>
        have hTermNN :
            term_has_non_none_type
              (SmtTerm.str_substr s (SmtTerm.Numeral 0)
                (SmtTerm.str_indexof_re_split s r1 r2)) := by
          unfold term_has_non_none_type
          simpa [__eo_to_smt_re_unfold_pos_component] using hNN
        rcases str_substr_args_of_non_none hTermNN with ⟨T, hS, hStart, hLen⟩
        have hSplitNN :
            term_has_non_none_type (SmtTerm.str_indexof_re_split s r1 r2) := by
          unfold term_has_non_none_type
          rw [hLen]
          simp
        have hSplitArgs := str_indexof_re_split_args_of_non_none hSplitNN
        have hT : T = SmtType.Char := by
          cases hS.symm.trans hSplitArgs.1
          rfl
        rw [typeof_str_substr_eq, hS, hStart, hLen, hT]
        simp [__smtx_typeof_str_substr]
  | succ n ih =>
      cases r <;> simp [__eo_to_smt_re_unfold_pos_component] at hNN ⊢
      case re_concat r1 r2 =>
        exact ih _ r2 hNN

/-- Applying a regex-unfold component as a function is ill-typed. -/
private theorem typeof_apply_re_unfold_pos_component_head_eq_none
    (s r : SmtTerm) (n : native_Nat) (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (__eo_to_smt_re_unfold_pos_component s r n) x) =
      SmtType.None := by
  exact typeof_generic_apply_non_function_head_eq_none _ _
    (generic_apply_type_of_non_special_head _ _
      (by intro s' d i j h; exact eo_to_smt_re_unfold_ne_dt_sel s r n s' d i j h)
      (by intro s' d i h; exact eo_to_smt_re_unfold_ne_dt_tester s r n s' d i h))
    (by
      intro A B hFun
      have hNN : __smtx_typeof (__eo_to_smt_re_unfold_pos_component s r n) ≠ SmtType.None := by
        rw [hFun]
        simp
      have hTy := smtx_typeof_re_unfold_pos_component_of_non_none s r n hNN
      rw [hTy] at hFun
      cases hFun)
    (by
      intro A B hIFun
      have hNN : __smtx_typeof (__eo_to_smt_re_unfold_pos_component s r n) ≠ SmtType.None := by
        rw [hIFun]
        simp
      have hTy := smtx_typeof_re_unfold_pos_component_of_non_none s r n hNN
      rw [hTy] at hIFun
      cases hIFun)
    (by
      intro A B hDtc
      have hNN : __smtx_typeof (__eo_to_smt_re_unfold_pos_component s r n) ≠ SmtType.None := by
        rw [hDtc]
        simp
      have hTy := smtx_typeof_re_unfold_pos_component_of_non_none s r n hNN
      rw [hTy] at hDtc
      cases hDtc)

/-- Applying the top-level regex-unfold component witness as a function is ill-typed. -/
private theorem typeof_apply_re_unfold_top_eq_none
    (t r idx x : Term) :
    __smtx_typeof
        (SmtTerm.Apply (__eo_to_smt (Term._at_re_unfold_pos_component t r idx))
          (__eo_to_smt x)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.Apply
          (native_ite (__eo_to_smt_nat_is_valid idx)
            (__eo_to_smt_re_unfold_pos_component (__eo_to_smt t) (__eo_to_smt r)
              (__eo_to_smt_nat idx))
            SmtTerm.None)
          (__eo_to_smt x)) =
      SmtType.None
  cases hValid : __eo_to_smt_nat_is_valid idx <;>
    simp [native_ite, typeof_apply_none_eq,
      typeof_apply_re_unfold_pos_component_head_eq_none]

/-- Extracts the top-level string and regex types from the base regex-unfold component. -/
private theorem re_unfold_pos_component_zero_args_of_non_none
    (s r1 r2 : SmtTerm)
    (hNN :
      term_has_non_none_type
        (__eo_to_smt_re_unfold_pos_component s (SmtTerm.re_concat r1 r2) native_nat_zero)) :
    __smtx_typeof s = SmtType.Seq SmtType.Char ∧
      __smtx_typeof (SmtTerm.re_concat r1 r2) = SmtType.RegLan := by
  have hTermNN :
      term_has_non_none_type
        (SmtTerm.str_substr s (SmtTerm.Numeral 0)
          (SmtTerm.str_indexof_re_split s r1 r2)) := by
    simpa [__eo_to_smt_re_unfold_pos_component] using hNN
  rcases str_substr_args_of_non_none hTermNN with ⟨T, hS, hStart, hLen⟩
  have hSplitNN : term_has_non_none_type (SmtTerm.str_indexof_re_split s r1 r2) := by
    unfold term_has_non_none_type
    rw [hLen]
    simp
  have hSplitArgs := str_indexof_re_split_args_of_non_none hSplitNN
  have hR : __smtx_typeof (SmtTerm.re_concat r1 r2) = SmtType.RegLan := by
    rw [typeof_re_concat_eq]
    simp [hSplitArgs.2.1, hSplitArgs.2.2, native_ite, native_Teq]
  exact ⟨hSplitArgs.1, hR⟩

/-- Extracts the top-level string and regex types from a regex-unfold component. -/
private theorem re_unfold_pos_component_args_of_non_none
    (s r : SmtTerm)
    (n : native_Nat)
    (hNN : term_has_non_none_type (__eo_to_smt_re_unfold_pos_component s r n)) :
    __smtx_typeof s = SmtType.Seq SmtType.Char ∧
      __smtx_typeof r = SmtType.RegLan := by
  induction n generalizing s r with
  | zero =>
      cases r <;> simp [__eo_to_smt_re_unfold_pos_component] at hNN
      case re_concat r1 r2 =>
        exact re_unfold_pos_component_zero_args_of_non_none s r1 r2 (by
          simpa [__eo_to_smt_re_unfold_pos_component] using hNN)
      all_goals
        exfalso
        unfold term_has_non_none_type at hNN
        exact hNN smtx_typeof_none
  | succ n ih =>
      cases r <;> simp [__eo_to_smt_re_unfold_pos_component] at hNN
      case re_concat r1 r2 =>
        let v0 := SmtTerm.str_indexof_re_split s r1 r2
        let newS := SmtTerm.str_substr s v0 (SmtTerm.neg (SmtTerm.str_len s) v0)
        have hRecArgs :
            __smtx_typeof newS = SmtType.Seq SmtType.Char ∧
              __smtx_typeof r2 = SmtType.RegLan := by
          exact ih newS r2 (by
            simpa [newS, v0, __eo_to_smt_re_unfold_pos_component] using hNN)
        have hNewSNN : term_has_non_none_type newS := by
          unfold term_has_non_none_type
          rw [hRecArgs.1]
          simp
        rcases str_substr_args_of_non_none hNewSNN with ⟨T, hSRaw, hV0, hLen⟩
        have hSplitNN : term_has_non_none_type v0 := by
          unfold term_has_non_none_type
          rw [hV0]
          simp
        have hSplitArgs := str_indexof_re_split_args_of_non_none hSplitNN
        have hR : __smtx_typeof (SmtTerm.re_concat r1 r2) = SmtType.RegLan := by
          rw [typeof_re_concat_eq]
          simp [hSplitArgs.2.1, hSplitArgs.2.2, native_ite, native_Teq]
        exact ⟨hSplitArgs.1, hR⟩
      all_goals
        exfalso
        unfold term_has_non_none_type at hNN
        exact hNN smtx_typeof_none

/-- Computes `__smtx_typeof` for `not` terms. -/
private theorem smtx_typeof_not_bool_or_none
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.not t) = SmtType.Bool ∨
      __smtx_typeof (SmtTerm.not t) = SmtType.None := by
  cases hT : __smtx_typeof t <;>
    (rw [typeof_not_eq]; simp [hT, native_ite, native_Teq])

/-- Computes `__smtx_typeof` for `exists` terms. -/
private theorem smtx_typeof_exists_bool_or_none
    (s : native_String) (T : SmtType) (body : SmtTerm) :
    __smtx_typeof (SmtTerm.exists s T body) = SmtType.Bool ∨
      __smtx_typeof (SmtTerm.exists s T body) = SmtType.None := by
  rw [typeof_exists_eq]
  cases hBody : __smtx_typeof body <;>
    simp [native_ite, native_Teq]
  cases hWf : __smtx_type_wf T <;>
    simp [__smtx_typeof_guard_wf, native_ite, hWf]

/-- `None` is not Boolean-typed. -/
theorem smtx_typeof_none_ne_bool :
    __smtx_typeof SmtTerm.None ≠ SmtType.Bool := by
  simp [smtx_typeof_none]

/-- A Boolean `not` term has a Boolean argument. -/
theorem smtx_typeof_not_arg_bool
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.not t) = SmtType.Bool ->
    __smtx_typeof t = SmtType.Bool := by
  intro hTy
  rw [typeof_not_eq] at hTy
  by_cases hArg : __smtx_typeof t = SmtType.Bool
  · exact hArg
  · cases hTest : native_Teq (__smtx_typeof t) SmtType.Bool <;>
      simp [hTest, native_ite] at hTy
    simpa [native_Teq] using hTest

/-- Computes the EO type of a variable-headed list cons once the tail is a list. -/
theorem eo_typeof_list_cons_var
    (s : native_String) (T xs : Term)
    (hTail : __eo_typeof xs = Term.__eo_List) :
    __eo_typeof (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) xs) =
      Term.__eo_List := by
  change
    __eo_typeof_apply
      (Term.Apply (Term.Apply Term.FunType Term.__eo_List) Term.__eo_List)
      (__eo_typeof xs) = Term.__eo_List
  rw [hTail]
  rfl

/-- Pulls the body Boolean fact back through nested `__eo_to_smt_exists`. -/
theorem eo_to_smt_exists_body_bool_of_bool
    (xs : Term) (body : SmtTerm) :
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool ->
    __smtx_typeof body = SmtType.Bool := by
  intro hTy
  cases hxs : xs
  case __eo_List_nil =>
    subst hxs
    simpa [__eo_to_smt_exists] using hTy
  case Apply f a =>
    subst hxs
    cases hf : f
    case Apply g y =>
      subst hf
      cases hg : g
      case __eo_List_cons =>
        subst hg
        cases hy : y
        case Var name T =>
          subst hy
          cases hname : name
          case String s =>
            subst hname
            have hExistsTy :
                __smtx_typeof (SmtTerm.exists s (__eo_to_smt_type T) (__eo_to_smt_exists a body)) =
                  SmtType.Bool := by
              simpa [__eo_to_smt_exists] using hTy
            have hNN :
                term_has_non_none_type (SmtTerm.exists s (__eo_to_smt_type T) (__eo_to_smt_exists a body)) := by
              unfold term_has_non_none_type
              rw [hExistsTy]
              simp
            have hSub : __smtx_typeof (__eo_to_smt_exists a body) = SmtType.Bool := by
              simpa using exists_body_bool_of_non_none hNN
            exact eo_to_smt_exists_body_bool_of_bool a body hSub
          all_goals
            subst hname
            have hNone := hTy
            simp [smtx_typeof_none, __eo_to_smt_exists] at hNone
        all_goals
          subst hy
          have hNone := hTy
          simp [smtx_typeof_none, __eo_to_smt_exists] at hNone
      all_goals
        subst hg
        have hNone := hTy
        simp [smtx_typeof_none, __eo_to_smt_exists] at hNone
    all_goals
      subst hf
      have hNone := hTy
      simp [smtx_typeof_none, __eo_to_smt_exists] at hNone
  all_goals
    subst hxs
    have hNone := hTy
    simp [smtx_typeof_none, __eo_to_smt_exists] at hNone

/-- Recovers EO list typing from a Boolean SMT existential chain. -/
theorem eo_typeof_var_list_of_exists_bool
    (xs : Term) (body : SmtTerm) :
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool ->
    __eo_typeof xs = Term.__eo_List := by
  intro hTy
  cases hxs : xs
  case __eo_List_nil =>
    subst hxs
    rfl
  case Apply f a =>
    subst hxs
    cases hf : f
    case Apply g y =>
      subst hf
      cases hg : g
      case __eo_List_cons =>
        subst hg
        cases hy : y
        case Var name T =>
          subst hy
          cases hname : name
          case String s =>
            subst hname
            have hExistsTy :
                __smtx_typeof (SmtTerm.exists s (__eo_to_smt_type T) (__eo_to_smt_exists a body)) =
                  SmtType.Bool := by
              simpa [__eo_to_smt_exists] using hTy
            have hNN :
                term_has_non_none_type (SmtTerm.exists s (__eo_to_smt_type T) (__eo_to_smt_exists a body)) := by
              unfold term_has_non_none_type
              rw [hExistsTy]
              simp
            have hSub : __smtx_typeof (__eo_to_smt_exists a body) = SmtType.Bool := by
              simpa using exists_body_bool_of_non_none hNN
            have hTail : __eo_typeof a = Term.__eo_List :=
              eo_typeof_var_list_of_exists_bool a body hSub
            exact eo_typeof_list_cons_var s T a hTail
          all_goals
            subst hname
            have hNone := hTy
            simp [smtx_typeof_none, __eo_to_smt_exists] at hNone
        all_goals
          subst hy
          have hNone := hTy
          simp [smtx_typeof_none, __eo_to_smt_exists] at hNone
      all_goals
        subst hg
        have hNone := hTy
        simp [smtx_typeof_none, __eo_to_smt_exists] at hNone
    all_goals
      subst hf
      have hNone := hTy
      simp [smtx_typeof_none, __eo_to_smt_exists] at hNone
  all_goals
    subst hxs
    have hNone := hTy
    simp [smtx_typeof_none, __eo_to_smt_exists] at hNone

/-- Computes `__smtx_typeof` for top-level translated `exists`. -/
private theorem smtx_typeof_eo_to_smt_exists_top_bool_or_none
    (x y : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.exists) y) x)) =
        SmtType.Bool ∨
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.exists) y) x)) =
        SmtType.None := by
  cases y
  case __eo_List_nil =>
    right
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact smtx_typeof_none
  case Apply f tail =>
    cases f
    case Apply g head =>
      cases g
      case __eo_List_cons =>
        cases head
        case Var name T =>
          cases name
          case String s =>
            change
              __smtx_typeof
                    (SmtTerm.exists s (__eo_to_smt_type T)
                      (__eo_to_smt_exists tail (__eo_to_smt x))) =
                  SmtType.Bool ∨
                __smtx_typeof
                    (SmtTerm.exists s (__eo_to_smt_type T)
                      (__eo_to_smt_exists tail (__eo_to_smt x))) =
                  SmtType.None
            exact smtx_typeof_exists_bool_or_none s (__eo_to_smt_type T)
              (__eo_to_smt_exists tail (__eo_to_smt x))
          all_goals
            right
            change __smtx_typeof SmtTerm.None = SmtType.None
            exact smtx_typeof_none
        all_goals
          right
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none
      all_goals
        right
        change __smtx_typeof SmtTerm.None = SmtType.None
        exact smtx_typeof_none
    all_goals
      right
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact smtx_typeof_none
  all_goals
    right
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact smtx_typeof_none

/-- Computes `__smtx_typeof` for top-level translated `forall`. -/
private theorem smtx_typeof_eo_to_smt_forall_top_bool_or_none
    (x y : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.forall) y) x)) =
        SmtType.Bool ∨
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.forall) y) x)) =
        SmtType.None := by
  cases y
  case __eo_List_nil =>
    right
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact smtx_typeof_none
  all_goals
    change
      __smtx_typeof
          (SmtTerm.not (__eo_to_smt_exists _ (SmtTerm.not (__eo_to_smt x)))) =
          SmtType.Bool ∨
        __smtx_typeof
          (SmtTerm.not (__eo_to_smt_exists _ (SmtTerm.not (__eo_to_smt x)))) =
          SmtType.None
    exact smtx_typeof_not_bool_or_none
      (__eo_to_smt_exists _ (SmtTerm.not (__eo_to_smt x)))

/-- Proof for `exists`, using the body IH and quantifier-list inversion. -/
private theorem eo_to_smt_typeof_matches_translation_apply_exists_from_ih
    (x y : Term)
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.exists) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.exists) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.exists) y) x)) := by
  rcases smtx_typeof_eo_to_smt_exists_top_bool_or_none x y with hBool | hNone
  · have hChain : __smtx_typeof (__eo_to_smt_exists y (__eo_to_smt x)) = SmtType.Bool := by
      cases y
      case __eo_List_nil =>
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
      all_goals
        change __smtx_typeof (__eo_to_smt_exists _ (__eo_to_smt x)) = SmtType.Bool at hBool
        exact hBool
    have hList : __eo_typeof y = Term.__eo_List :=
      eo_typeof_var_list_of_exists_bool y (__eo_to_smt x) hChain
    have hXBoolSmt : __smtx_typeof (__eo_to_smt x) = SmtType.Bool :=
      eo_to_smt_exists_body_bool_of_bool y (__eo_to_smt x) hChain
    have hXBool : __eo_typeof x = Term.Bool :=
      eo_typeof_eq_bool_of_smt_bool_from_ih x ihX hXBoolSmt
    have hEo :
        __eo_to_smt_type
            (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.exists) y) x)) =
          SmtType.Bool := by
      change __eo_to_smt_type (__eo_typeof_forall (__eo_typeof y) (__eo_typeof x)) =
        SmtType.Bool
      rw [hList, hXBool]
      rfl
    exact hBool.trans hEo.symm
  · exact False.elim (hNonNone hNone)

/-- Proof for `forall`, using the body IH and quantifier-list inversion. -/
private theorem eo_to_smt_typeof_matches_translation_apply_forall_from_ih
    (x y : Term)
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.forall) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.forall) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.forall) y) x)) := by
  rcases smtx_typeof_eo_to_smt_forall_top_bool_or_none x y with hBool | hNone
  · have hChain :
        __smtx_typeof (__eo_to_smt_exists y (SmtTerm.not (__eo_to_smt x))) =
          SmtType.Bool := by
      cases y
      case __eo_List_nil =>
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
      all_goals
        refine smtx_typeof_not_arg_bool _ ?_
        exact hBool
    have hList : __eo_typeof y = Term.__eo_List :=
      eo_typeof_var_list_of_exists_bool y (SmtTerm.not (__eo_to_smt x)) hChain
    have hNotBoolSmt : __smtx_typeof (SmtTerm.not (__eo_to_smt x)) = SmtType.Bool :=
      eo_to_smt_exists_body_bool_of_bool y (SmtTerm.not (__eo_to_smt x)) hChain
    have hXBoolSmt : __smtx_typeof (__eo_to_smt x) = SmtType.Bool :=
      smtx_typeof_not_arg_bool (__eo_to_smt x) hNotBoolSmt
    have hXBool : __eo_typeof x = Term.Bool :=
      eo_typeof_eq_bool_of_smt_bool_from_ih x ihX hXBoolSmt
    have hEo :
        __eo_to_smt_type
            (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.forall) y) x)) =
          SmtType.Bool := by
      change __eo_to_smt_type (__eo_typeof_forall (__eo_typeof y) (__eo_typeof x)) =
        SmtType.Bool
      rw [hList, hXBool]
      rfl
    exact hBool.trans hEo.symm
  · exact False.elim (hNonNone hNone)

/-- Computes `__smtx_typeof` for `and` terms. -/
private theorem smtx_typeof_and_bool_or_none
    (s t : SmtTerm) :
    __smtx_typeof (SmtTerm.and s t) = SmtType.Bool ∨
      __smtx_typeof (SmtTerm.and s t) = SmtType.None := by
  cases hs : __smtx_typeof s <;>
    cases ht : __smtx_typeof t <;>
      (rw [typeof_and_eq]; simp [hs, ht, native_ite, native_Teq])

/-- Computes `__smtx_typeof` for `__eo_to_smt_distinct`. -/
private theorem smtx_typeof_eo_to_smt_distinct_bool_or_none
    (xs : Term) :
    __smtx_typeof (__eo_to_smt_distinct xs) = SmtType.Bool ∨
      __smtx_typeof (__eo_to_smt_distinct xs) = SmtType.None := by
  cases xs
  case Apply f a =>
    cases f
    case UOp op =>
      cases op with
      | _at__at_TypedList_nil =>
          left
          change __smtx_typeof (SmtTerm.Boolean true) = SmtType.Bool
          rw [__smtx_typeof.eq_1]
      | _ =>
          right
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none
    case Apply g b =>
      cases g
      case UOp op =>
        cases op with
        | _at__at_TypedList_cons =>
            change
              __smtx_typeof
                  (SmtTerm.and (__eo_to_smt_distinct_pairs (__eo_to_smt b) a)
                    (__eo_to_smt_distinct a)) = SmtType.Bool ∨
                __smtx_typeof
                  (SmtTerm.and (__eo_to_smt_distinct_pairs (__eo_to_smt b) a)
                    (__eo_to_smt_distinct a)) = SmtType.None
            exact smtx_typeof_and_bool_or_none
              (__eo_to_smt_distinct_pairs (__eo_to_smt b) a)
              (__eo_to_smt_distinct a)
        | _ =>
            right
            change __smtx_typeof SmtTerm.None = SmtType.None
            exact smtx_typeof_none
      all_goals
        right
        change __smtx_typeof SmtTerm.None = SmtType.None
        exact smtx_typeof_none
    all_goals
      right
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact smtx_typeof_none
  all_goals
    right
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact smtx_typeof_none

/-- Computes `__smtx_typeof_apply` for translated `distinct`. -/
private theorem smtx_typeof_apply_eo_to_smt_distinct_eq_none
    (xs : Term) (X : SmtType) :
    __smtx_typeof_apply (__smtx_typeof (__eo_to_smt_distinct xs)) X = SmtType.None := by
  rcases smtx_typeof_eo_to_smt_distinct_bool_or_none xs with hBool | hNone
  · rw [hBool]
    simp [__smtx_typeof_apply]
  · rw [hNone]
    simp [__smtx_typeof_apply]

/-- Computes `__smtx_typeof` for applying translated `distinct`. -/
private theorem smtx_typeof_eo_to_smt_distinct_apply_eq_none
    (xs : Term) (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (__eo_to_smt_distinct xs) x) = SmtType.None := by
  have hGeneric : generic_apply_type (__eo_to_smt_distinct xs) x :=
    generic_apply_type_of_non_special_head _ _
      (by intro s d i j h; exact eo_to_smt_distinct_ne_dt_sel xs s d i j h)
      (by intro s d i h; exact eo_to_smt_distinct_ne_dt_tester xs s d i h)
  rw [hGeneric]
  exact smtx_typeof_apply_eo_to_smt_distinct_eq_none xs (__smtx_typeof x)

/-- Applying a top-level translated `distinct` as a function is ill-typed. -/
private theorem smtx_typeof_eo_to_smt_distinct_top_apply_eq_none
    (xs : Term) (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.UOp UserOp.distinct) xs)) x) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.Apply
          (native_ite
            (native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None)
            SmtTerm.None (__eo_to_smt_distinct xs)) x) =
      SmtType.None
  cases hGuard : native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None
  · simp [native_ite]
    exact smtx_typeof_eo_to_smt_distinct_apply_eq_none xs x
  · simp [native_ite]
    exact typeof_apply_none_eq x

private theorem eo_get_nil_rec_ne_stuck_of_is_list_true
    {f x : Term}
    (h : __eo_is_list f x = Term.Boolean true) :
    __eo_get_nil_rec f x ≠ Term.Stuck := by
  by_cases hf : f = Term.Stuck
  · subst f
    simp [__eo_is_list] at h
  by_cases hx : x = Term.Stuck
  · subst x
    simp [__eo_is_list] at h
  cases hGet : __eo_get_nil_rec f x <;>
    simp [__eo_is_list, __eo_is_ok, hGet, native_teq, native_not,
      SmtEval.native_not] at h ⊢

theorem eo_tuple_is_list_true_of_smt_tuple_type :
    ∀ {T : Term} {d : SmtDatatype},
      __eo_to_smt_type T = SmtType.Datatype (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl d) ->
        __eo_is_list (Term.UOp UserOp.Tuple) T = Term.Boolean true
  | T, d, h => by
      rcases eo_to_smt_type_eq_tuple_datatype h with hUnit | hCons
      · rcases hUnit with ⟨hEq, _hd⟩
        subst T
        simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil, __eo_requires,
          __eo_is_ok, native_ite, native_teq, native_not, SmtEval.native_not]
      · rcases hCons with ⟨y, x0, c, hEq, hTail, _hd⟩
        subst T
        have hTailList :=
          eo_tuple_is_list_true_of_smt_tuple_type
            (T := x0) (d := SmtDatatype.sum c SmtDatatype.null) hTail
        have hTailGet :
            __eo_get_nil_rec (Term.UOp UserOp.Tuple) x0 ≠ Term.Stuck :=
          eo_get_nil_rec_ne_stuck_of_is_list_true hTailList
        simp [__eo_is_list, __eo_get_nil_rec, __eo_requires, __eo_is_ok,
          hTailGet, native_ite, native_teq, native_not, SmtEval.native_not]
termination_by T d h => T

private theorem eo_tuple_list_len_rec_eq_numeral_of_smt_tuple_type :
    ∀ {T : Term} {d : SmtDatatype},
      __eo_to_smt_type T = SmtType.Datatype (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl d) ->
        ∃ n : native_Int, __eo_list_len_rec T = Term.Numeral n
  | T, d, h => by
      rcases eo_to_smt_type_eq_tuple_datatype h with hUnit | hCons
      · rcases hUnit with ⟨hEq, _hd⟩
        subst T
        exact ⟨0, by simp [__eo_list_len_rec]⟩
      · rcases hCons with ⟨y, x0, c, hEq, hTail, _hd⟩
        subst T
        rcases
          eo_tuple_list_len_rec_eq_numeral_of_smt_tuple_type
            (T := x0) (d := SmtDatatype.sum c SmtDatatype.null) hTail with
          ⟨n, hLen⟩
        exact ⟨native_zplus 1 n, by simp [__eo_list_len_rec, hLen, __eo_add]⟩
termination_by T d h => T

theorem eo_tuple_list_len_ok_of_smt_tuple_type
    {T : Term} {d : SmtDatatype}
    (h : __eo_to_smt_type T = SmtType.Datatype (native_string_lit "@Tuple")
      (__eo_to_smt_tuple_decl d)) :
    __eo_is_ok (__eo_list_len (Term.UOp UserOp.Tuple) T) = Term.Boolean true := by
  have hList :
      __eo_is_list (Term.UOp UserOp.Tuple) T = Term.Boolean true :=
    eo_tuple_is_list_true_of_smt_tuple_type h
  rcases eo_tuple_list_len_rec_eq_numeral_of_smt_tuple_type h with ⟨n, hLen⟩
  simp [__eo_list_len, __eo_requires, __eo_is_ok, hList, hLen, native_ite,
    native_teq, native_not, SmtEval.native_not]

/- The following tuple-substitution development belongs to the old embedded
datatype representation.  Tuple declarations now carry their body explicitly
and selector typing uses declaration lookup/resolution.
private theorem eo_to_smt_type_tuple_eq_tuple_datatype_of_wf
    {A B : SmtType}
    (hWf : __smtx_type_wf (__eo_to_smt_type_tuple A B) = true) :
    ∃ d, __eo_to_smt_type_tuple A B = SmtType.Datatype (native_string_lit "@Tuple") d := by
  cases B <;> simp [__eo_to_smt_type_tuple, __smtx_type_wf,
    __smtx_type_wf_rec, native_and] at hWf ⊢
  case Datatype s d =>
    by_cases hs : s = (native_string_lit "@Tuple")
    · subst s
      cases d with
      | null =>
          simp [
            __smtx_type_wf_rec] at hWf
      | sum c rest =>
          cases rest with
          | null =>
              by_cases hComp :
                  (native_inhabited_type A = true ∧
                    __smtx_type_wf_rec A A = true) ∧
                      __smtx_type_no_alias_rec native_reflist_nil A = true
              · exact ⟨
                  SmtDatatype.sum (SmtDatatypeCons.cons A c) SmtDatatype.null,
                  by
                    simp [hComp.1.1, hComp.1.2, hComp.2, native_streq,
                      native_ite]⟩
              · exfalso
                simp [hComp,
                  __smtx_type_wf_rec,
                  native_ite] at hWf
          | sum c' rest' =>
              simp [
                __smtx_type_wf_rec] at hWf
    · cases d with
      | null =>
          simp [
            __smtx_type_wf_rec] at hWf
      | sum c rest =>
          cases rest <;> simp [hs,
            __smtx_type_wf_rec, native_streq, native_ite] at hWf

mutual

private theorem smtx_type_substitute_top_apply_tuple_of_eo_valid_rec
    (base : SmtDatatype) :
    {refs : RefList} -> (native_string_lit "@Tuple") ∉ refs -> {T : Term} ->
      eo_type_valid_rec refs T ->
        smtx_type_substitute_top_apply (native_string_lit "@Tuple") base (__eo_to_smt_type T) =
          __eo_to_smt_type T
  | refs, hNo, Term.Bool, _hValid => by
      simp [__eo_to_smt_type, smtx_type_substitute_top_apply]
  | refs, hNo, Term.DatatypeType s d, hValid => by
      rcases hValid with ⟨hReserved, hD⟩
      have hNe : s ≠ (native_string_lit "@Tuple") := by
        intro hs
        subst s
        rw [eo_reserved_datatype_name_tuple] at hReserved
        cases hReserved
      have hNo' : (native_string_lit "@Tuple") ∉ s :: refs := by
        intro hMem
        simp at hMem
        rcases hMem with hEq | hMem
        · exact hNe hEq.symm
        · exact hNo hMem
      have hDSub :
          __smtx_dt_substitute (native_string_lit "@Tuple")
              (__smtx_dt_lift s (__eo_to_smt_datatype d) base) (__eo_to_smt_datatype d) =
            __eo_to_smt_datatype d :=
        smtx_dt_substitute_tuple_of_eo_datatype_valid_rec
          (__smtx_dt_lift s (__eo_to_smt_datatype d) base) hNo' hD
      simp [__eo_to_smt_type, hReserved, smtx_type_substitute_top_apply,
        native_ite, native_streq, hDSub]
  | refs, hNo, Term.DatatypeTypeRef s, hValid => by
      rcases hValid with ⟨hReserved, _hMem⟩
      have hNe : s ≠ (native_string_lit "@Tuple") := by
        intro hs
        subst s
        rw [eo_reserved_datatype_name_tuple] at hReserved
        cases hReserved
      have hTupleNe : (native_string_lit "@Tuple") ≠ s := by
        intro hs
        exact hNe hs.symm
      simp [__eo_to_smt_type, hReserved, smtx_type_substitute_top_apply,
        native_ite, native_streq, hTupleNe]
  | refs, hNo, Term.DtcAppType T U, hValid => by
      rcases hValid with ⟨hT, hU⟩
      have hTNN : __eo_to_smt_type T ≠ SmtType.None :=
        eo_type_valid_rec_non_none hT
      have hUNN : __eo_to_smt_type U ≠ SmtType.None :=
        eo_type_valid_rec_non_none hU
      simp [__eo_to_smt_type, hTNN, hUNN, __smtx_typeof_guard,
        smtx_type_substitute_top_apply, native_ite, native_Teq]
  | refs, hNo, Term.USort i, _hValid => by
      simp [__eo_to_smt_type, smtx_type_substitute_top_apply]
  | refs, hNo, Term.Apply (Term.Apply Term.FunType T) U, hValid => by
      rcases (by simpa [eo_type_valid_rec] using hValid :
        eo_type_valid_rec [] T ∧ eo_type_valid_rec [] U) with ⟨hT, hU⟩
      have hTNN : __eo_to_smt_type T ≠ SmtType.None :=
        eo_type_valid_rec_non_none hT
      have hUNN : __eo_to_smt_type U ≠ SmtType.None :=
        eo_type_valid_rec_non_none hU
      simp [eo_to_smt_type_fun, hTNN, hUNN, __smtx_typeof_guard,
        smtx_type_substitute_top_apply, native_ite, native_Teq]
  | refs, hNo, Term.UOp UserOp.Int, _hValid => by
      simp [__eo_to_smt_type, smtx_type_substitute_top_apply]
  | refs, hNo, Term.UOp UserOp.Real, _hValid => by
      simp [__eo_to_smt_type, smtx_type_substitute_top_apply]
  | refs, hNo, Term.UOp UserOp.Char, _hValid => by
      simp [__eo_to_smt_type, smtx_type_substitute_top_apply]
  | refs, hNo, Term.UOp UserOp.UnitTuple, _hValid => by
      simp [__eo_to_smt_type, smtx_type_substitute_top_apply, native_ite, native_streq]
  | refs, hNo, Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n), hValid => by
      have hn : native_zleq 0 n = true := by
        simpa [eo_type_valid_rec] using hValid
      simp [__eo_to_smt_type, hn, smtx_type_substitute_top_apply, native_ite]
  | refs, hNo, Term.Apply (Term.UOp UserOp.Seq) T, hValid => by
      have hT : eo_type_valid_rec [] T := by
        simpa [eo_type_valid_rec] using hValid
      have hTNN : __eo_to_smt_type T ≠ SmtType.None :=
        eo_type_valid_rec_non_none hT
      simp [__eo_to_smt_type, hTNN, __smtx_typeof_guard,
        smtx_type_substitute_top_apply, native_ite, native_Teq]
  | refs, hNo, Term.Apply (Term.Apply (Term.UOp UserOp.Array) T) U, hValid => by
      rcases (by simpa [eo_type_valid_rec] using hValid :
        eo_type_valid_rec [] T ∧ eo_type_valid_rec [] U) with ⟨hT, hU⟩
      have hTNN : __eo_to_smt_type T ≠ SmtType.None :=
        eo_type_valid_rec_non_none hT
      have hUNN : __eo_to_smt_type U ≠ SmtType.None :=
        eo_type_valid_rec_non_none hU
      simp [__eo_to_smt_type, hTNN, hUNN, __smtx_typeof_guard,
        smtx_type_substitute_top_apply, native_ite, native_Teq]
  | refs, hNo, Term.Apply (Term.UOp UserOp.Set) T, hValid => by
      have hT : eo_type_valid_rec [] T := by
        simpa [eo_type_valid_rec] using hValid
      have hTNN : __eo_to_smt_type T ≠ SmtType.None :=
        eo_type_valid_rec_non_none hT
      simp [__eo_to_smt_type, hTNN, __smtx_typeof_guard,
        smtx_type_substitute_top_apply, native_ite, native_Teq]
  | refs, hNo, Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T) U, hValid => by
      rcases (by simpa [eo_type_valid_rec] using hValid :
        eo_type_valid_rec [] T ∧ eo_type_valid_rec [] U ∧
          __smtx_type_wf
            (__eo_to_smt_type_tuple (__eo_to_smt_type T) (__eo_to_smt_type U)) =
            true) with ⟨_hT, _hU, hWf⟩
      rcases eo_to_smt_type_tuple_eq_tuple_datatype_of_wf hWf with ⟨d, hRaw⟩
      have hWfRaw : __smtx_type_wf (SmtType.Datatype (native_string_lit "@Tuple") d) = true := by
        simpa [hRaw] using hWf
      change
        smtx_type_substitute_top_apply (native_string_lit "@Tuple") base
            (native_ite
              (__smtx_type_wf
                (__eo_to_smt_type_tuple (__eo_to_smt_type T) (__eo_to_smt_type U)))
              (__eo_to_smt_type_tuple (__eo_to_smt_type T) (__eo_to_smt_type U))
              SmtType.None) =
          native_ite
            (__smtx_type_wf
              (__eo_to_smt_type_tuple (__eo_to_smt_type T) (__eo_to_smt_type U)))
            (__eo_to_smt_type_tuple (__eo_to_smt_type T) (__eo_to_smt_type U))
            SmtType.None
      simp [native_ite, hRaw, hWfRaw, smtx_type_substitute_top_apply,
        native_streq]
  | refs, hNo, T, hValid => by
      cases T with
      | Bool =>
          simp [__eo_to_smt_type, smtx_type_substitute_top_apply]
      | USort i =>
          simp [__eo_to_smt_type, smtx_type_substitute_top_apply]
      | UOp op =>
          cases op <;> simp [eo_type_valid_rec, __eo_to_smt_type,
            smtx_type_substitute_top_apply, native_ite, native_streq] at hValid ⊢
      | DatatypeType s d =>
          rcases hValid with ⟨hReserved, hD⟩
          have hNe : s ≠ (native_string_lit "@Tuple") := by
            intro hs
            subst s
            rw [eo_reserved_datatype_name_tuple] at hReserved
            cases hReserved
          have hNo' : (native_string_lit "@Tuple") ∉ s :: refs := by
            intro hMem
            simp at hMem
            rcases hMem with hEq | hMem
            · exact hNe hEq.symm
            · exact hNo hMem
          have hDSub :
              __smtx_dt_substitute (native_string_lit "@Tuple")
                  (__smtx_dt_lift s (__eo_to_smt_datatype d) base) (__eo_to_smt_datatype d) =
                __eo_to_smt_datatype d :=
            smtx_dt_substitute_tuple_of_eo_datatype_valid_rec
              (__smtx_dt_lift s (__eo_to_smt_datatype d) base) hNo' hD
          simp [__eo_to_smt_type, hReserved, smtx_type_substitute_top_apply,
            native_ite, native_streq, hDSub]
      | DatatypeTypeRef s =>
          rcases hValid with ⟨hReserved, _hMem⟩
          have hNe : s ≠ (native_string_lit "@Tuple") := by
            intro hs
            subst s
            rw [eo_reserved_datatype_name_tuple] at hReserved
            cases hReserved
          have hTupleNe : (native_string_lit "@Tuple") ≠ s := by
            intro hs
            exact hNe hs.symm
          simp [__eo_to_smt_type, hReserved, smtx_type_substitute_top_apply,
            native_ite, native_streq, hTupleNe]
      | DtcAppType T U =>
          rcases hValid with ⟨hT, hU⟩
          have hTNN : __eo_to_smt_type T ≠ SmtType.None :=
            eo_type_valid_rec_non_none hT
          have hUNN : __eo_to_smt_type U ≠ SmtType.None :=
            eo_type_valid_rec_non_none hU
          simp [__eo_to_smt_type, hTNN, hUNN, __smtx_typeof_guard,
            smtx_type_substitute_top_apply, native_ite, native_Teq]
      | Apply f x =>
          cases f with
          | UOp op =>
              cases op <;>
                try simp [eo_type_valid_rec] at hValid
              case BitVec =>
                cases x with
                | Numeral n =>
                    have hn : native_zleq 0 n = true := by
                      simpa [eo_type_valid_rec] using hValid
                    simp [__eo_to_smt_type, hn, smtx_type_substitute_top_apply,
                      native_ite]
                | _ =>
                    simp [eo_type_valid_rec] at hValid
              case Seq =>
                have hx : eo_type_valid_rec [] x := by
                  simpa [eo_type_valid_rec] using hValid
                have hxNN : __eo_to_smt_type x ≠ SmtType.None :=
                  eo_type_valid_rec_non_none hx
                simp [__eo_to_smt_type, hxNN, __smtx_typeof_guard,
                  smtx_type_substitute_top_apply, native_ite, native_Teq]
              case Set =>
                have hx : eo_type_valid_rec [] x := by
                  simpa [eo_type_valid_rec] using hValid
                have hxNN : __eo_to_smt_type x ≠ SmtType.None :=
                  eo_type_valid_rec_non_none hx
                simp [__eo_to_smt_type, hxNN, __smtx_typeof_guard,
                  smtx_type_substitute_top_apply, native_ite, native_Teq]
          | Apply g y =>
              cases g with
              | FunType =>
                  rcases (by simpa [eo_type_valid_rec] using hValid :
                    eo_type_valid_rec [] y ∧ eo_type_valid_rec [] x) with ⟨hy, hx⟩
                  have hyNN : __eo_to_smt_type y ≠ SmtType.None :=
                    eo_type_valid_rec_non_none hy
                  have hxNN : __eo_to_smt_type x ≠ SmtType.None :=
                    eo_type_valid_rec_non_none hx
                  simp [eo_to_smt_type_fun, hyNN, hxNN, __smtx_typeof_guard,
                    smtx_type_substitute_top_apply, native_ite, native_Teq]
              | UOp op =>
                  cases op <;>
                    try simp [eo_type_valid_rec] at hValid
                  case Array =>
                    rcases (by simpa [eo_type_valid_rec] using hValid :
                      eo_type_valid_rec [] y ∧ eo_type_valid_rec [] x) with ⟨hy, hx⟩
                    have hyNN : __eo_to_smt_type y ≠ SmtType.None :=
                      eo_type_valid_rec_non_none hy
                    have hxNN : __eo_to_smt_type x ≠ SmtType.None :=
                      eo_type_valid_rec_non_none hx
                    simp [__eo_to_smt_type, hyNN, hxNN, __smtx_typeof_guard,
                      smtx_type_substitute_top_apply, native_ite, native_Teq]
                  case Tuple =>
                    rcases (by simpa [eo_type_valid_rec] using hValid :
                      eo_type_valid_rec [] y ∧ eo_type_valid_rec [] x ∧
                        __smtx_type_wf
                          (__eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x)) =
                          true) with ⟨_hy, _hx, hWf⟩
                    rcases eo_to_smt_type_tuple_eq_tuple_datatype_of_wf hWf with ⟨d, hRaw⟩
                    have hWfRaw :
                        __smtx_type_wf (SmtType.Datatype (native_string_lit "@Tuple") d) = true := by
                      simpa [hRaw] using hWf
                    change
                      smtx_type_substitute_top_apply (native_string_lit "@Tuple") base
                          (native_ite
                            (__smtx_type_wf
                              (__eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x)))
                            (__eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x))
                            SmtType.None) =
                        native_ite
                          (__smtx_type_wf
                            (__eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x)))
                          (__eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x))
                          SmtType.None
                    simp [native_ite, hRaw, hWfRaw, smtx_type_substitute_top_apply,
                      native_streq]
              | _ =>
                  simp [eo_type_valid_rec] at hValid
          | _ =>
              simp [eo_type_valid_rec] at hValid
      | _ =>
          simp [eo_type_valid_rec] at hValid

private theorem smtx_dtc_substitute_tuple_of_eo_datatype_cons_valid_rec
    (base : SmtDatatype) :
    {refs : RefList} -> (native_string_lit "@Tuple") ∉ refs -> {c : DatatypeCons} ->
      eo_datatype_cons_valid_rec refs c ->
        __smtx_dtc_substitute (native_string_lit "@Tuple") base (__eo_to_smt_datatype_cons c) =
          __eo_to_smt_datatype_cons c
  | refs, hNo, DatatypeCons.unit, _hValid => by
      simp [__eo_to_smt_datatype_cons, __smtx_dtc_substitute]
  | refs, hNo, DatatypeCons.cons T c, hValid => by
      rcases hValid with ⟨hT, hC⟩
      have hTSub :
          smtx_type_substitute_top_apply (native_string_lit "@Tuple") base (__eo_to_smt_type T) =
            __eo_to_smt_type T :=
        smtx_type_substitute_top_apply_tuple_of_eo_valid_rec
          base hNo hT
      have hCSub :
          __smtx_dtc_substitute (native_string_lit "@Tuple") base (__eo_to_smt_datatype_cons c) =
            __eo_to_smt_datatype_cons c :=
        smtx_dtc_substitute_tuple_of_eo_datatype_cons_valid_rec
          base hNo hC
      cases hTy : __eo_to_smt_type T <;>
        simp [__eo_to_smt_datatype_cons, __smtx_dtc_substitute,
          smtx_type_substitute_top_apply, hTy, hCSub, native_ite,
          native_streq] at hTSub ⊢
      all_goals exact hTSub

private theorem smtx_dt_substitute_tuple_of_eo_datatype_valid_rec
    (base : SmtDatatype) :
    {refs : RefList} -> (native_string_lit "@Tuple") ∉ refs -> {d : Datatype} ->
      eo_datatype_valid_rec refs d ->
        __smtx_dt_substitute (native_string_lit "@Tuple") base (__eo_to_smt_datatype d) =
          __eo_to_smt_datatype d
  | refs, hNo, Datatype.null, _hValid => by
      simp [__eo_to_smt_datatype, __smtx_dt_substitute]
  | refs, hNo, Datatype.sum c d, hValid => by
      rcases hValid with ⟨hC, hD⟩
      have hCSub :
          __smtx_dtc_substitute (native_string_lit "@Tuple") base (__eo_to_smt_datatype_cons c) =
            __eo_to_smt_datatype_cons c :=
        smtx_dtc_substitute_tuple_of_eo_datatype_cons_valid_rec
          base hNo hC
      have hDSub :
          __smtx_dt_substitute (native_string_lit "@Tuple") base (__eo_to_smt_datatype d) =
            __eo_to_smt_datatype d :=
        smtx_dt_substitute_tuple_of_eo_datatype_valid_rec
          base hNo hD
      simp [__eo_to_smt_datatype, __smtx_dt_substitute, hCSub, hDSub]

end

theorem smtx_type_substitute_top_apply_tuple_of_eo_valid
    (base : SmtDatatype) {T : Term}
    (hValid : eo_type_valid T) :
    smtx_type_substitute_top_apply (native_string_lit "@Tuple") base (__eo_to_smt_type T) =
      __eo_to_smt_type T := by
  cases T with
  | UOp op =>
      cases op with
      | Int =>
          have hNo : ((native_string_lit "@Tuple") : native_String) ∉ ([] : RefList) := by
            intro h
            exact List.not_mem_nil h
          exact
            smtx_type_substitute_top_apply_tuple_of_eo_valid_rec
              base (refs := []) (T := Term.UOp UserOp.Int) hNo
              (by simpa [eo_type_valid] using hValid)
      | Real =>
          have hNo : ((native_string_lit "@Tuple") : native_String) ∉ ([] : RefList) := by
            intro h
            exact List.not_mem_nil h
          exact
            smtx_type_substitute_top_apply_tuple_of_eo_valid_rec
              base (refs := []) (T := Term.UOp UserOp.Real) hNo
              (by simpa [eo_type_valid] using hValid)
      | Char =>
          have hNo : ((native_string_lit "@Tuple") : native_String) ∉ ([] : RefList) := by
            intro h
            exact List.not_mem_nil h
          exact
            smtx_type_substitute_top_apply_tuple_of_eo_valid_rec
              base (refs := []) (T := Term.UOp UserOp.Char) hNo
              (by simpa [eo_type_valid] using hValid)
      | UnitTuple =>
          have hNo : ((native_string_lit "@Tuple") : native_String) ∉ ([] : RefList) := by
            intro h
            exact List.not_mem_nil h
          exact
            smtx_type_substitute_top_apply_tuple_of_eo_valid_rec
              base (refs := []) (T := Term.UOp UserOp.UnitTuple) hNo
              (by simpa [eo_type_valid] using hValid)
      | RegLan =>
          simp [__eo_to_smt_type, smtx_type_substitute_top_apply
            ]
      | _ =>
          exfalso
          simp [eo_type_valid, eo_type_valid_rec] at hValid
  | _ =>
      have hNo : ((native_string_lit "@Tuple") : native_String) ∉ ([] : RefList) := by
        intro h
        exact List.not_mem_nil h
      exact
        smtx_type_substitute_top_apply_tuple_of_eo_valid_rec
          base (refs := []) hNo (by simpa [eo_type_valid] using hValid)

-/

private theorem smtx_ret_typeof_tuple_sel_rec_eq_eo_list_nth_rec_nat :
    ∀ {T : Term} {d : SmtDatatype} (j : native_Nat),
      __eo_to_smt_type T = SmtType.Datatype (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl d) ->
      __smtx_ret_typeof_sel_rec d native_nat_zero j =
        __eo_to_smt_type
          (__eo_list_nth_rec T (Term.Numeral (native_nat_to_int j)))
  | T, d, j, hT => by
      rcases eo_to_smt_type_eq_tuple_datatype hT with hUnit | hCons
      · rcases hUnit with ⟨hEq, hD⟩
        subst T
        have hdBody :
            d = SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null := by
          simpa [__eo_to_smt_tuple_decl] using hD
        subst d
        cases j <;>
          simp [__smtx_ret_typeof_sel_rec, __eo_list_nth_rec,
            __eo_to_smt_type, native_nat_to_int, Smtm.native_nat_to_int]
      · rcases hCons with ⟨y, x0, c, hEq, hTail, hD⟩
        subst T
        have hdBody :
            d = SmtDatatype.sum
                (SmtDatatypeCons.cons (__eo_to_smt_type y) c)
                SmtDatatype.null := by
          simpa [__eo_to_smt_tuple_decl] using hD
        subst d
        cases j with
        | zero =>
            simp [__smtx_ret_typeof_sel_rec, __eo_list_nth_rec,
              native_nat_to_int, Smtm.native_nat_to_int]
        | succ j =>
            have hStep :
                native_zplus (native_nat_to_int (native_nat_succ j)) (-1 : native_Int) =
                  native_nat_to_int j := by
              have hInt : ((j : Int) + 1) + (-1 : Int) = j := by
                omega
              simpa [native_zplus, SmtEval.native_zplus, native_nat_to_int,
                Smtm.native_nat_to_int] using hInt
            have hNe :
                native_nat_to_int (native_nat_succ j) ≠ (0 : native_Int) := by
              have hInt : ((j : Int) + 1) ≠ 0 := by
                omega
              simpa [native_nat_to_int, Smtm.native_nat_to_int] using hInt
            have hIH :=
              smtx_ret_typeof_tuple_sel_rec_eq_eo_list_nth_rec_nat
                (T := x0) (d := SmtDatatype.sum c SmtDatatype.null) j hTail
            have hNth :
                __eo_list_nth_rec
                    (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) y) x0)
                    (Term.Numeral (native_nat_to_int (native_nat_succ j))) =
                  __eo_list_nth_rec x0 (Term.Numeral (native_nat_to_int j)) := by
              simpa [__eo_add, hStep] using
                (__eo_list_nth_rec.eq_3
                  (Term.Numeral (native_nat_to_int (native_nat_succ j)))
                  (Term.UOp UserOp.Tuple) y x0
                  (by intro h; cases h)
                  (by
                    intro h
                    injection h with hInt
                    exact hNe hInt))
            rw [hNth]
            simpa [__smtx_ret_typeof_sel_rec] using hIH
termination_by T d j hT => T

/-- Resolving a synthetic tuple declaration is a no-op on its body.  Every
field was produced by EO type translation and admitted by tuple component
well-formedness, so no field can be a bare SMT `TypeRef`. -/
theorem smtx_dt_resolve_tuple_body_eq :
    ∀ {T : Term} {d : SmtDatatype},
      __eo_to_smt_type T = SmtType.Datatype (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl d) →
      ∀ dd : SmtDatatypeDecl, __smtx_dt_resolve d dd = d
  | T, d, hT, dd => by
      rcases eo_to_smt_type_eq_tuple_datatype hT with hUnit | hCons
      · rcases hUnit with ⟨hEq, hD⟩
        subst T
        have hdBody :
            d = SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null := by
          simpa [__eo_to_smt_tuple_decl] using hD
        subst d
        simp [__smtx_dt_resolve, __smtx_dtc_resolve]
      · rcases hCons with ⟨y, x0, c, hEq, hTail, hD⟩
        subst T
        have hdBody :
            d = SmtDatatype.sum
                (SmtDatatypeCons.cons (__eo_to_smt_type y) c)
                SmtDatatype.null := by
          simpa [__eo_to_smt_tuple_decl] using hD
        subst d
        have hRawWf :
            __smtx_type_wf
                (__eo_to_smt_type_tuple (__eo_to_smt_type y)
                  (__eo_to_smt_type x0)) = true := by
          change native_ite
              (__smtx_type_wf
                (__eo_to_smt_type_tuple (__eo_to_smt_type y)
                  (__eo_to_smt_type x0)))
              (__eo_to_smt_type_tuple (__eo_to_smt_type y)
                (__eo_to_smt_type x0)) SmtType.None = _ at hT
          cases hw : __smtx_type_wf
              (__eo_to_smt_type_tuple (__eo_to_smt_type y)
                (__eo_to_smt_type x0)) <;>
            simp [native_ite, hw] at hT ⊢
        have hRaw :
            __eo_to_smt_type_tuple (__eo_to_smt_type y)
                (__eo_to_smt_type x0) =
              SmtType.Datatype (native_string_lit "@Tuple")
                (__eo_to_smt_tuple_decl
                  (SmtDatatype.sum
                    (SmtDatatypeCons.cons (__eo_to_smt_type y) c)
                    SmtDatatype.null)) := by
          change native_ite
              (__smtx_type_wf
                (__eo_to_smt_type_tuple (__eo_to_smt_type y)
                  (__eo_to_smt_type x0)))
              (__eo_to_smt_type_tuple (__eo_to_smt_type y)
                (__eo_to_smt_type x0)) SmtType.None = _ at hT
          simpa [native_ite, hRawWf] using hT
        have hyComp :
            __smtx_type_wf_component (__eo_to_smt_type y) = true := by
          by_cases hc : __smtx_type_wf_component (__eo_to_smt_type y) = true
          · exact hc
          · have hcF : __smtx_type_wf_component (__eo_to_smt_type y) = false :=
              Bool.eq_false_iff.mpr hc
            have hRawNone :
                __eo_to_smt_type_tuple (__eo_to_smt_type y)
                    (__eo_to_smt_type x0) = SmtType.None := by
              rw [hTail]
              change native_ite
                  (native_and
                    (native_and
                      (native_streq (native_string_lit "@Tuple")
                        (native_string_lit "@Tuple"))
                      (native_streq (native_string_lit "@Tuple")
                        (native_string_lit "@Tuple")))
                    (__smtx_type_wf_component (__eo_to_smt_type y))) _
                  SmtType.None = SmtType.None
              rw [hcF]
              simp [native_and, native_streq, native_ite]
            rw [hRawNone] at hRawWf
            simp [__smtx_type_wf, __smtx_type_wf_component,
              __smtx_type_wf_rec, native_and] at hRawWf
        have hyNotRef : ∀ r, __eo_to_smt_type y ≠ SmtType.TypeRef r := by
          intro r hr
          rw [hr] at hyComp
          simp [__smtx_type_wf_component, __smtx_type_wf_rec, native_and] at hyComp
        have hTailResolve := smtx_dt_resolve_tuple_body_eq
          (T := x0) (d := SmtDatatype.sum c SmtDatatype.null) hTail dd
        have hCResolve : __smtx_dtc_resolve c dd = c := by
          simpa [__smtx_dt_resolve] using hTailResolve
        have hHeadResolve :
            __smtx_dtc_resolve
                (SmtDatatypeCons.cons (__eo_to_smt_type y) c) dd =
              SmtDatatypeCons.cons (__eo_to_smt_type y) c := by
          cases hy : __eo_to_smt_type y <;>
            simp [__smtx_dtc_resolve, hy, hCResolve] at hyNotRef ⊢
        simp [__smtx_dt_resolve, hHeadResolve]
termination_by T d hT dd => T

/- Obsolete: selector return types now resolve their datatype declaration
instead of substituting a datatype body.
private theorem smtx_type_substitute_top_apply_tuple_of_eo_list_nth_rec_nat :
    ∀ {T : Term} {d base : SmtDatatype} (j : native_Nat),
      __eo_to_smt_type T = SmtType.Datatype (native_string_lit "@Tuple") d ->
        eo_type_valid_rec [] T ->
          smtx_type_substitute_top_apply (native_string_lit "@Tuple") base
              (__eo_to_smt_type
                (__eo_list_nth_rec T (Term.Numeral (native_nat_to_int j)))) =
            __eo_to_smt_type
              (__eo_list_nth_rec T (Term.Numeral (native_nat_to_int j)))
  | T, d, base, j, hT, hValid => by
      rcases eo_to_smt_type_eq_tuple_datatype hT with hUnit | hCons
      · rcases hUnit with ⟨hEq, hD⟩
        subst T
        cases j <;>
          simp [__eo_list_nth_rec, smtx_type_substitute_top_apply,
            __eo_to_smt_type, native_nat_to_int, Smtm.native_nat_to_int
            ]
      · rcases hCons with ⟨y, x0, c, hEq, hTail, hD⟩
        subst T
        have hOuter := hValid
        unfold eo_type_valid_rec at hOuter
        rw [hT] at hOuter
        have hp :
            noNoneTy (__eo_to_smt_type y) = true ∧
              noNoneDtc c = true := by
          simpa [__eo_to_smt_tuple_decl, noNoneTy, noNoneDecl,
            noNoneDt, noNoneDtc, native_and] using hOuter
        have hy : eo_type_valid_rec [] y := by
          simpa [eo_type_valid_rec] using hp.1
        have hx : eo_type_valid_rec [] x0 := by
          unfold eo_type_valid_rec
          rw [hTail]
          simp [__eo_to_smt_tuple_decl, noNoneTy, noNoneDecl,
            noNoneDt, native_and, hp.2]
        cases j with
        | zero =>
            exact
              smtx_type_substitute_top_apply_tuple_of_eo_valid_rec
                base (by simp) hy
        | succ j =>
            have hStep :
                native_zplus (native_nat_to_int (native_nat_succ j)) (-1 : native_Int) =
                  native_nat_to_int j := by
              have hInt : ((j : Int) + 1) + (-1 : Int) = j := by
                omega
              simpa [native_zplus, SmtEval.native_zplus, native_nat_to_int,
                Smtm.native_nat_to_int] using hInt
            have hNe :
                native_nat_to_int (native_nat_succ j) ≠ (0 : native_Int) := by
              have hInt : ((j : Int) + 1) ≠ 0 := by
                omega
              simpa [native_nat_to_int, Smtm.native_nat_to_int] using hInt
            have hIH :=
              smtx_type_substitute_top_apply_tuple_of_eo_list_nth_rec_nat
                (T := x0) (d := SmtDatatype.sum c SmtDatatype.null) (base := base)
                j hTail hx
            have hNth :
                __eo_list_nth_rec
                    (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) y) x0)
                    (Term.Numeral (native_nat_to_int (native_nat_succ j))) =
                  __eo_list_nth_rec x0 (Term.Numeral (native_nat_to_int j)) := by
              simpa [__eo_add, hStep] using
                (__eo_list_nth_rec.eq_3
                  (Term.Numeral (native_nat_to_int (native_nat_succ j)))
                  (Term.UOp UserOp.Tuple) y x0
                  (by intro h; cases h)
                  (by
                    intro h
                    injection h with hInt
                    exact hNe hInt))
            rw [hNth]
            exact hIH
termination_by T d base j hT hValid => T

-/

theorem eo_type_valid_rec_of_tuple_smt_type
    {T : Term} {d : SmtDatatype}
    (_hT : __eo_to_smt_type T = SmtType.Datatype (native_string_lit "@Tuple")
      (__eo_to_smt_tuple_decl d))
    (hValid : eo_type_valid T) :
    eo_type_valid_rec [] T := by
  simpa [eo_type_valid, eo_type_valid_rec] using hValid

theorem eo_type_valid_rec_tuple_list_nth_rec_nat :
    ∀ {T : Term} {d : SmtDatatype} (j : native_Nat),
      __eo_to_smt_type T = SmtType.Datatype (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl d) ->
        eo_type_valid_rec [] T ->
          j < __smtx_dt_num_sels d native_nat_zero ->
            eo_type_valid_rec []
              (__eo_list_nth_rec T (Term.Numeral (native_nat_to_int j)))
  | T, d, j, hT, hValid, hj => by
      rcases eo_to_smt_type_eq_tuple_datatype hT with hUnit | hCons
      · rcases hUnit with ⟨hEq, hD⟩
        subst T
        have hdBody :
            d = SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null := by
          simpa [__eo_to_smt_tuple_decl] using hD
        subst d
        simp [__smtx_dt_num_sels, __smtx_dtc_num_sels] at hj
      · rcases hCons with ⟨y, x0, c, hEq, hTail, hD⟩
        subst T
        have hdBody :
            d = SmtDatatype.sum
                (SmtDatatypeCons.cons (__eo_to_smt_type y) c)
                SmtDatatype.null := by
          simpa [__eo_to_smt_tuple_decl] using hD
        subst d
        have hOuter := hValid
        unfold eo_type_valid_rec at hOuter
        rw [hT] at hOuter
        have hp :
            noNoneTy (__eo_to_smt_type y) = true ∧ noNoneDtc c = true := by
          simpa [__eo_to_smt_tuple_decl, noNoneTy, noNoneDecl,
            noNoneDt, noNoneDtc, native_and] using hOuter
        have hy : eo_type_valid_rec [] y := by
          simpa [eo_type_valid_rec] using hp.1
        have hx : eo_type_valid_rec [] x0 := by
          unfold eo_type_valid_rec
          rw [hTail]
          simp [__eo_to_smt_tuple_decl, noNoneTy, noNoneDecl,
            noNoneDt, native_and, hp.2]
        cases j with
        | zero =>
            simpa [__eo_list_nth_rec, native_nat_to_int, Smtm.native_nat_to_int] using hy
        | succ j =>
            have hjTail : j < __smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null)
                native_nat_zero := by
              simpa [__smtx_dt_num_sels, __smtx_dtc_num_sels] using hj
            have hStep :
                native_zplus (native_nat_to_int (native_nat_succ j)) (-1 : native_Int) =
                  native_nat_to_int j := by
              have hInt : ((j : Int) + 1) + (-1 : Int) = j := by
                omega
              simpa [native_zplus, SmtEval.native_zplus, native_nat_to_int,
                Smtm.native_nat_to_int] using hInt
            have hNe :
                native_nat_to_int (native_nat_succ j) ≠ (0 : native_Int) := by
              have hInt : ((j : Int) + 1) ≠ 0 := by
                omega
              simpa [native_nat_to_int, Smtm.native_nat_to_int] using hInt
            have hNth :
                __eo_list_nth_rec
                    (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) y) x0)
                    (Term.Numeral (native_nat_to_int (native_nat_succ j))) =
                  __eo_list_nth_rec x0 (Term.Numeral (native_nat_to_int j)) := by
              simpa [__eo_add, hStep] using
                (__eo_list_nth_rec.eq_3
                  (Term.Numeral (native_nat_to_int (native_nat_succ j)))
                  (Term.UOp UserOp.Tuple) y x0
                  (by intro h; cases h)
                  (by
                    intro h
                    injection h with hInt
                    exact hNe hInt))
            rw [hNth]
            exact eo_type_valid_rec_tuple_list_nth_rec_nat
              (T := x0) (d := SmtDatatype.sum c SmtDatatype.null) j hTail hx hjTail
termination_by T d j hT hValid hj => T

theorem smtx_ret_typeof_tuple_sel_eq_eo_list_nth_rec_nat
    {T : Term} {d : SmtDatatype} (j : native_Nat)
    (hT : __eo_to_smt_type T = SmtType.Datatype (native_string_lit "@Tuple")
      (__eo_to_smt_tuple_decl d))
    (hValid : eo_type_valid_rec [] T) :
    __smtx_ret_typeof_sel (native_string_lit "@Tuple")
      (__eo_to_smt_tuple_decl d) native_nat_zero j =
      __eo_to_smt_type (__eo_list_nth_rec T (Term.Numeral (native_nat_to_int j))) := by
  unfold __smtx_ret_typeof_sel
  have hResolve := smtx_dt_resolve_tuple_body_eq
    (T := T) (d := d) hT (__eo_to_smt_tuple_decl d)
  have hLookup :
      __smtx_dd_lookup (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl d) = d := by
    simp [__eo_to_smt_tuple_decl, __smtx_dd_lookup, native_streq,
      SmtEval.native_streq, native_ite]
  rw [hLookup, hResolve]
  exact smtx_ret_typeof_tuple_sel_rec_eq_eo_list_nth_rec_nat j hT

private def smtx_apply_head : SmtTerm -> SmtTerm
  | SmtTerm.Apply f _ => smtx_apply_head f
  | t => t

private def smtx_num_apply_args : SmtTerm -> Nat
  | SmtTerm.Apply f _ => Nat.succ (smtx_num_apply_args f)
  | _ => 0

private theorem smtx_apply_arg_non_none_of_generic_apply_non_none
    (f x : SmtTerm)
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i)
    (hNN : __smtx_typeof (SmtTerm.Apply f x) ≠ SmtType.None) :
    __smtx_typeof x ≠ SmtType.None := by
  have hApply :
      __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None := by
    cases f
    case DtSel s d i j =>
      exact False.elim (hSel s d i j rfl)
    case DtTester s d i =>
      exact False.elim (hTester s d i rfl)
    all_goals
      simpa [__smtx_typeof] using hNN
  rcases typeof_apply_non_none_cases hApply with ⟨A, _B, _hHead, hArg, hA, _hB⟩
  rw [hArg]
  exact hA

private theorem smtx_apply_head_non_none_of_generic_apply_non_none
    (f x : SmtTerm)
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i)
    (hNN : __smtx_typeof (SmtTerm.Apply f x) ≠ SmtType.None) :
    __smtx_typeof f ≠ SmtType.None := by
  have hApply :
      __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None := by
    cases f
    case DtSel s d i j =>
      exact False.elim (hSel s d i j rfl)
    case DtTester s d i =>
      exact False.elim (hTester s d i rfl)
    all_goals
      simpa [__smtx_typeof] using hNN
  rcases typeof_apply_non_none_cases hApply with ⟨A, B, hHead, _hArg, _hA, _hB⟩
  rcases hHead with hHead | hHead
  · rw [hHead]
    simp
  · rw [hHead]
    simp

private theorem smtx_dt_cons_chain_type_of_non_none_aux :
    ∀ (n : Nat) (t : SmtTerm) (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat),
      smtx_num_apply_args t = n ->
      smtx_apply_head t = SmtTerm.DtCons s d i ->
      __smtx_typeof t ≠ SmtType.None ->
      __smtx_typeof t =
        dt_cons_applied_type_rec s d
          (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
          (smtx_num_apply_args t) := by
  intro n
  induction n with
  | zero =>
      intro t s d i hN hHead hNN
      cases t <;> simp [smtx_num_apply_args, smtx_apply_head] at hN hHead
      case DtCons s' d' i' =>
      rcases hHead with ⟨rfl, hEq⟩
      rcases hEq with ⟨rfl, rfl⟩
      rw [typeof_dt_cons_eq]
      have hGuard :
          __smtx_typeof_guard_wf (SmtType.Datatype s' d')
              (__smtx_typeof_dt_cons_rec
                (SmtType.Datatype s' d')
                (__smtx_dt_resolve (__smtx_dd_lookup s' d') d') i') =
            __smtx_typeof_dt_cons_rec
              (SmtType.Datatype s' d')
              (__smtx_dt_resolve (__smtx_dd_lookup s' d') d') i' :=
        smtx_typeof_guard_wf_of_non_none
          (SmtType.Datatype s' d')
          (__smtx_typeof_dt_cons_rec
            (SmtType.Datatype s' d')
            (__smtx_dt_resolve (__smtx_dd_lookup s' d') d') i')
          (by simpa [typeof_dt_cons_eq] using hNN)
      simp [hGuard, smtx_num_apply_args, dt_cons_applied_type_rec,
        typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec]
  | succ n ih =>
      intro t s d i hN hHead hNN
      cases t <;> simp [smtx_num_apply_args, smtx_apply_head] at hN hHead
      case Apply f a =>
      have hHeadF : smtx_apply_head f = SmtTerm.DtCons s d i := by
        simpa using hHead
      have hRecSel : ∀ s0 d0 i0 j0, f ≠ SmtTerm.DtSel s0 d0 i0 j0 := by
        intro s0 d0 i0 j0 hf
        subst f
        simp [smtx_apply_head] at hHeadF
      have hRecTester : ∀ s0 d0 i0, f ≠ SmtTerm.DtTester s0 d0 i0 := by
        intro s0 d0 i0 hf
        subst f
        simp [smtx_apply_head] at hHeadF
      have hGeneric : generic_apply_type f a :=
        generic_apply_type_of_non_special_head f a hRecSel hRecTester
      have hApplyNN :
          __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof a) ≠ SmtType.None := by
        unfold generic_apply_type at hGeneric
        rw [hGeneric] at hNN
        exact hNN
      rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHeadTy, hArg, hA, _hB⟩
      have hFunNN : __smtx_typeof f ≠ SmtType.None := by
        rcases hHeadTy with hHeadTy | hHeadTy
        · rw [hHeadTy]
          simp
        · rw [hHeadTy]
          simp
      have ihEq := ih f s d i hN hHeadF hFunNN
      have hlt :
          smtx_num_apply_args f <
            __smtx_dt_num_sels (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i := by
        rcases hHeadTy with hHeadTy | hHeadTy
        · have hArgs := congrArg dt_cons_type_num_args hHeadTy
          rw [ihEq, dt_cons_type_num_args_dt_cons_applied_type_rec] at hArgs
          simp [dt_cons_type_num_args] at hArgs
          omega
        · have hArgs := congrArg dt_cons_type_num_args hHeadTy
          rw [ihEq, dt_cons_type_num_args_dt_cons_applied_type_rec] at hArgs
          simp [dt_cons_type_num_args] at hArgs
          omega
      let R := __smtx_ret_typeof_sel_rec
        (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
        (smtx_num_apply_args f)
      let Rest :=
        dt_cons_applied_type_rec s d
          (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
          (Nat.succ (smtx_num_apply_args f))
      have hStep :
          dt_cons_applied_type_rec s d
              (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
              (smtx_num_apply_args f) =
            SmtType.DtcAppType R Rest := by
        simpa [R, Rest] using
          dt_cons_applied_type_rec_step s d
            (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
            (smtx_num_apply_args f) hlt
      have hArgR : __smtx_typeof a = R := by
        rcases hHeadTy with hHeadTy | hHeadTy
        · have hBad : SmtType.DtcAppType R Rest = SmtType.FunType A B := by
            exact (ihEq.trans hStep).symm.trans hHeadTy
          cases hBad
        · have hCmp : SmtType.DtcAppType R Rest = SmtType.DtcAppType A B := by
            exact (ihEq.trans hStep).symm.trans hHeadTy
          injection hCmp with hAeq _hBeq
          exact hArg.trans hAeq.symm
      have hRNN : R ≠ SmtType.None := by
        rw [← hArgR]
        rw [hArg]
        exact hA
      have hApplyTy : __smtx_typeof (SmtTerm.Apply f a) = Rest := by
        rw [hGeneric]
        exact smtx_typeof_apply_of_head_cases (Or.inr (ihEq.trans hStep)) hArgR hRNN
      simpa [smtx_num_apply_args, Rest] using hApplyTy

private theorem smtx_dt_cons_chain_type_of_non_none :
    ∀ {t : SmtTerm} {s : native_String} {d : SmtDatatypeDecl} {i : native_Nat},
      smtx_apply_head t = SmtTerm.DtCons s d i ->
      __smtx_typeof t ≠ SmtType.None ->
      __smtx_typeof t =
        dt_cons_applied_type_rec s d
          (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
          (smtx_num_apply_args t)
  | t, s, d, i, hHead, hNN =>
      smtx_dt_cons_chain_type_of_non_none_aux
        (smtx_num_apply_args t) t s d i rfl hHead hNN

private theorem smtx_term_typeof_full_dt_cons_chain_apply
    {t : SmtTerm}
    {s : native_String}
    {d : SmtDatatypeDecl}
    {i : native_Nat}
    (hHead : smtx_apply_head t = SmtTerm.DtCons s d i)
    (hCount :
      smtx_num_apply_args t =
        __smtx_dt_num_sels (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i)
    (hNN : __smtx_typeof t ≠ SmtType.None) :
    __smtx_typeof t = SmtType.Datatype s d := by
  have hChain := smtx_dt_cons_chain_type_of_non_none hHead hNN
  have hRecNN :
      dt_cons_applied_type_rec s d
          (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
          (smtx_num_apply_args t) ≠
        SmtType.None := by
    intro hNone
    apply hNN
    rw [hChain, hNone]
  have hFull :
      dt_cons_applied_type_rec s d
          (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
          (__smtx_dt_num_sels (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i) =
        SmtType.Datatype s d :=
    dt_cons_applied_type_rec_full_arity s d
      (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
      (by simpa [hCount] using hRecNN)
  calc
    __smtx_typeof t =
        dt_cons_applied_type_rec s d
          (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
          (smtx_num_apply_args t) := hChain
    _ =
        dt_cons_applied_type_rec s d
          (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
          (__smtx_dt_num_sels (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i) := by
        rw [hCount]
    _ = SmtType.Datatype s d := hFull

private theorem smtx_tuple_prepend_rec_apply_head
    (tailDD : SmtDatatypeDecl) (tailD : SmtDatatype) (tail : SmtTerm) :
    ∀ (k : native_Nat) (acc : SmtTerm),
      smtx_apply_head (__eo_to_smt_tuple_prepend_rec tailDD tailD tail k acc) =
        smtx_apply_head acc
  | native_nat_zero, acc => by
      simp [__eo_to_smt_tuple_prepend_rec]
  | native_nat_succ k, acc => by
      simp [__eo_to_smt_tuple_prepend_rec, smtx_apply_head,
        smtx_tuple_prepend_rec_apply_head tailDD tailD tail k acc]

private theorem smtx_tuple_prepend_rec_num_apply_args
    (tailDD : SmtDatatypeDecl) (tailD : SmtDatatype) (tail : SmtTerm) :
    ∀ (k : native_Nat) (acc : SmtTerm),
      smtx_num_apply_args (__eo_to_smt_tuple_prepend_rec tailDD tailD tail k acc) =
        k + smtx_num_apply_args acc
  | native_nat_zero, acc => by
      simp [__eo_to_smt_tuple_prepend_rec]
  | native_nat_succ k, acc => by
      simp [__eo_to_smt_tuple_prepend_rec, smtx_num_apply_args,
        smtx_tuple_prepend_rec_num_apply_args tailDD tailD tail k acc, Nat.succ_add]

private theorem smtx_tuple_prepend_rec_seed_non_none_of_non_none
    (tailDD : SmtDatatypeDecl) (tailD : SmtDatatype) (tail : SmtTerm) :
    ∀ (k : native_Nat) (acc : SmtTerm),
      (∀ s d i j, acc ≠ SmtTerm.DtSel s d i j) ->
      (∀ s d i, acc ≠ SmtTerm.DtTester s d i) ->
      __smtx_typeof (__eo_to_smt_tuple_prepend_rec tailDD tailD tail k acc) ≠
        SmtType.None ->
        __smtx_typeof acc ≠ SmtType.None
  | native_nat_zero, acc, _hAccSel, _hAccTester, hNN => by
      simpa [__eo_to_smt_tuple_prepend_rec] using hNN
  | native_nat_succ k, acc, hAccSel, hAccTester, hNN => by
      have hRecNN :
          __smtx_typeof (__eo_to_smt_tuple_prepend_rec tailDD tailD tail k acc) ≠
            SmtType.None :=
        smtx_apply_head_non_none_of_generic_apply_non_none
          (__eo_to_smt_tuple_prepend_rec tailDD tailD tail k acc)
          (SmtTerm.Apply (SmtTerm.DtSel (native_string_lit "@Tuple") tailDD native_nat_zero k) tail)
          (eo_to_smt_tuple_prepend_rec_ne_dt_sel tailDD tailD tail k acc hAccSel)
          (eo_to_smt_tuple_prepend_rec_ne_dt_tester tailDD tailD tail k acc hAccTester)
          (by simpa [__eo_to_smt_tuple_prepend_rec] using hNN)
      exact
        smtx_tuple_prepend_rec_seed_non_none_of_non_none tailDD tailD tail k acc
          hAccSel hAccTester hRecNN

theorem smtx_tuple_prepend_typeof_of_tail_tuple_type
    (tail head : SmtTerm) (T : SmtType) (c : SmtDatatypeCons)
    (hTailTy :
      __smtx_typeof tail =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl (SmtDatatype.sum c SmtDatatype.null)))
    (hNN :
      __smtx_typeof (__eo_to_smt_tuple_prepend head T tail) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt_tuple_prepend head T tail) =
      SmtType.Datatype (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl
          (SmtDatatype.sum (SmtDatatypeCons.cons T c) SmtDatatype.null)) := by
  let tailD := SmtDatatype.sum c SmtDatatype.null
  let fullD := SmtDatatype.sum (SmtDatatypeCons.cons T c) SmtDatatype.null
  let tailDD := __eo_to_smt_tuple_decl tailD
  let fullDD := __eo_to_smt_tuple_decl fullD
  have hFullWf : __smtx_type_wf (SmtType.Datatype (native_string_lit "@Tuple") fullDD) = true := by
    cases hWf : __smtx_type_wf (SmtType.Datatype (native_string_lit "@Tuple") fullDD)
    · exfalso
      apply hNN
      unfold __eo_to_smt_tuple_prepend
      rw [hTailTy]
      dsimp [fullDD, fullD, __eo_to_smt_tuple_decl] at hWf
      simp [__eo_to_smt_tuple_prepend_of_type, __eo_to_smt_tuple_decl,
        native_streq, native_and, native_ite, hWf]
    · rfl
  dsimp [fullDD, fullD, __eo_to_smt_tuple_decl] at hFullWf
  let seed := SmtTerm.Apply
    (SmtTerm.DtCons (native_string_lit "@Tuple") fullDD native_nat_zero) head
  have hTerm :
      __eo_to_smt_tuple_prepend head T tail =
        __eo_to_smt_tuple_prepend_rec tailDD tailD tail
          (__smtx_dt_num_sels tailD native_nat_zero) seed := by
    unfold __eo_to_smt_tuple_prepend
    rw [hTailTy]
    simp [__eo_to_smt_tuple_prepend_of_type, __eo_to_smt_tuple_decl,
      tailD, fullD, tailDD, fullDD, seed, native_streq, native_and, native_ite,
      hFullWf]
  have hRecNN :
      __smtx_typeof
          (__eo_to_smt_tuple_prepend_rec tailDD tailD tail
            (__smtx_dt_num_sels tailD native_nat_zero) seed) ≠
        SmtType.None := by
    rw [← hTerm]
    exact hNN
  have hHead :
      smtx_apply_head
          (__eo_to_smt_tuple_prepend_rec tailDD tailD tail
            (__smtx_dt_num_sels tailD native_nat_zero) seed) =
        SmtTerm.DtCons (native_string_lit "@Tuple") fullDD native_nat_zero := by
    simp [smtx_tuple_prepend_rec_apply_head, smtx_apply_head, seed]
  have hCountPlain :
      smtx_num_apply_args
          (__eo_to_smt_tuple_prepend_rec tailDD tailD tail
            (__smtx_dt_num_sels tailD native_nat_zero) seed) =
        __smtx_dt_num_sels fullD native_nat_zero := by
    simp [smtx_tuple_prepend_rec_num_apply_args, smtx_num_apply_args,
      tailD, fullD, seed, __smtx_dt_num_sels, __smtx_dtc_num_sels]
  have hCount :
      smtx_num_apply_args
          (__eo_to_smt_tuple_prepend_rec tailDD tailD tail
            (__smtx_dt_num_sels tailD native_nat_zero) seed) =
        __smtx_dt_num_sels
          (__smtx_dt_resolve (__smtx_dd_lookup (native_string_lit "@Tuple") fullDD) fullDD)
          native_nat_zero := by
    rw [hCountPlain]
    simpa [fullDD, fullD, __eo_to_smt_tuple_decl, __smtx_dd_lookup,
      native_streq, SmtEval.native_streq, native_ite] using
      (dt_num_sels_resolve fullDD fullD native_nat_zero).symm
  have hRecTy :
      __smtx_typeof
          (__eo_to_smt_tuple_prepend_rec tailDD tailD tail
            (__smtx_dt_num_sels tailD native_nat_zero) seed) =
        SmtType.Datatype (native_string_lit "@Tuple") fullDD :=
    smtx_term_typeof_full_dt_cons_chain_apply hHead hCount hRecNN
  rw [hTerm]
  exact hRecTy

theorem smtx_tuple_prepend_head_non_none_of_tail_tuple_type
    (tail head : SmtTerm) (T : SmtType) (c : SmtDatatypeCons)
    (hTailTy :
      __smtx_typeof tail =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl (SmtDatatype.sum c SmtDatatype.null)))
    (hNN :
      __smtx_typeof (__eo_to_smt_tuple_prepend head T tail) ≠ SmtType.None) :
    __smtx_typeof head ≠ SmtType.None := by
  let tailD := SmtDatatype.sum c SmtDatatype.null
  let fullD := SmtDatatype.sum (SmtDatatypeCons.cons T c) SmtDatatype.null
  let tailDD := __eo_to_smt_tuple_decl tailD
  let fullDD := __eo_to_smt_tuple_decl fullD
  have hFullWf : __smtx_type_wf (SmtType.Datatype (native_string_lit "@Tuple") fullDD) = true := by
    cases hWf : __smtx_type_wf (SmtType.Datatype (native_string_lit "@Tuple") fullDD)
    · exfalso
      apply hNN
      unfold __eo_to_smt_tuple_prepend
      rw [hTailTy]
      dsimp [fullDD, fullD, __eo_to_smt_tuple_decl] at hWf
      simp [__eo_to_smt_tuple_prepend_of_type, __eo_to_smt_tuple_decl,
        native_streq, native_and, native_ite, hWf]
    · rfl
  dsimp [fullDD, fullD, __eo_to_smt_tuple_decl] at hFullWf
  let seed := SmtTerm.Apply
    (SmtTerm.DtCons (native_string_lit "@Tuple") fullDD native_nat_zero) head
  have hTerm :
      __eo_to_smt_tuple_prepend head T tail =
        __eo_to_smt_tuple_prepend_rec tailDD tailD tail
          (__smtx_dt_num_sels tailD native_nat_zero) seed := by
    unfold __eo_to_smt_tuple_prepend
    rw [hTailTy]
    simp [__eo_to_smt_tuple_prepend_of_type, __eo_to_smt_tuple_decl,
      tailD, fullD, tailDD, fullDD, seed, native_streq, native_and, native_ite,
      hFullWf]
  have hRecNN :
      __smtx_typeof
          (__eo_to_smt_tuple_prepend_rec tailDD tailD tail
            (__smtx_dt_num_sels tailD native_nat_zero) seed) ≠
        SmtType.None := by
    rw [← hTerm]
    exact hNN
  have hSeedNN : __smtx_typeof seed ≠ SmtType.None :=
    smtx_tuple_prepend_rec_seed_non_none_of_non_none tailDD tailD tail
      (__smtx_dt_num_sels tailD native_nat_zero) seed
      (by intro s d i j hSeed; simp [seed] at hSeed)
      (by intro s d i hSeed; simp [seed] at hSeed)
      hRecNN
  exact
    smtx_apply_arg_non_none_of_generic_apply_non_none
      (SmtTerm.DtCons (native_string_lit "@Tuple") fullDD native_nat_zero) head
      (by intro s d i j hSel; cases hSel)
      (by intro s d i hTester; cases hTester)
      (by simpa [seed] using hSeedNN)

/-- Simplifies EO-to-SMT translation for `tuple_select`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_tuple_select
    (x y : Term)
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.tuple_select y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.tuple_select y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.tuple_select y) x)) := by
  cases hTy : __smtx_typeof (__eo_to_smt x) with
  | Datatype s d =>
      by_cases hTuple : s = (native_string_lit "@Tuple")
      · subst s
        have hDecl : ∃ body, d = __eo_to_smt_tuple_decl body := by
          cases d with
          | nil =>
              exfalso
              apply hNonNone
              change
                __smtx_typeof
                    (__eo_to_smt_tuple_select
                      (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y)
                      (__eo_to_smt x)) = SmtType.None
              rw [hTy]
              cases __eo_to_smt y <;> simp [__eo_to_smt_tuple_select]
          | cons s2 body rest =>
              cases rest with
              | nil =>
                  by_cases hs2 : s2 = native_string_lit "@Tuple"
                  · subst s2
                    exact ⟨body, rfl⟩
                  · exfalso
                    apply hNonNone
                    change
                      __smtx_typeof
                          (__eo_to_smt_tuple_select
                            (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y)
                            (__eo_to_smt x)) = SmtType.None
                    rw [hTy]
                    cases __eo_to_smt y <;>
                      simp [__eo_to_smt_tuple_select, hs2, native_streq,
                        native_and, native_ite]
              | cons s3 body3 rest3 =>
                  exfalso
                  apply hNonNone
                  change
                    __smtx_typeof
                        (__eo_to_smt_tuple_select
                          (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y)
                          (__eo_to_smt x)) = SmtType.None
                  rw [hTy]
                  cases __eo_to_smt y <;> simp [__eo_to_smt_tuple_select]
        rcases hDecl with ⟨body, rfl⟩
        let tupleDD := __eo_to_smt_tuple_decl body
        cases hIdx : __eo_to_smt y with
        | Numeral n =>
            cases hNonneg : native_zleq 0 n
            · exact eo_to_smt_typeof_matches_translation_of_smt_none
                (Term.Apply (Term.UOp1 UserOp1.tuple_select y) x)
                (by
                  change
                    __smtx_typeof
                        (__eo_to_smt_tuple_select
                          (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y) (__eo_to_smt x)) =
                      SmtType.None
                  rw [hTy, hIdx]
                  simp [__eo_to_smt_tuple_select, __eo_to_smt_tuple_decl,
                    hNonneg, native_streq, native_and, native_ite])
                hNonNone
            · have hTranslate :
                  __eo_to_smt (Term.Apply (Term.UOp1 UserOp1.tuple_select y) x) =
                    SmtTerm.Apply
                      (SmtTerm.DtSel (native_string_lit "@Tuple") tupleDD native_nat_zero (native_int_to_nat n))
                      (__eo_to_smt x) := by
                change
                  __eo_to_smt_tuple_select
                      (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y) (__eo_to_smt x) =
                    SmtTerm.Apply
                      (SmtTerm.DtSel (native_string_lit "@Tuple") tupleDD native_nat_zero (native_int_to_nat n))
                      (__eo_to_smt x)
                rw [hTy, hIdx]
                simp [__eo_to_smt_tuple_select, __eo_to_smt_tuple_decl,
                  tupleDD, hNonneg, native_streq, native_and, native_ite]
              have hApplyNN :
                  term_has_non_none_type
                    (SmtTerm.Apply
                      (SmtTerm.DtSel (native_string_lit "@Tuple") tupleDD native_nat_zero (native_int_to_nat n))
                      (__eo_to_smt x)) := by
                unfold term_has_non_none_type
                rw [← hTranslate]
                exact hNonNone
              have hSmt :
                  __smtx_typeof
                      (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.tuple_select y) x)) =
                    __smtx_ret_typeof_sel (native_string_lit "@Tuple") tupleDD native_nat_zero (native_int_to_nat n) := by
                rw [hTranslate]
                exact dt_sel_term_typeof_of_non_none hApplyNN
              have hArgTy :
                  __smtx_typeof (__eo_to_smt x) = SmtType.Datatype (native_string_lit "@Tuple") tupleDD :=
                dt_sel_arg_datatype_of_non_none hApplyNN
              have hXNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
                rw [hArgTy]
                simp
              have hTyFromIH :
                  __eo_to_smt_type (__eo_typeof x) = SmtType.Datatype (native_string_lit "@Tuple") tupleDD := by
                exact (ihX hXNN).symm.trans hArgTy
              have hTyBody :
                  __eo_to_smt_type (__eo_typeof x) =
                    SmtType.Datatype (native_string_lit "@Tuple")
                      (__eo_to_smt_tuple_decl body) := by
                simpa [tupleDD] using hTyFromIH
              have hTNonNone :
                  __smtx_ret_typeof_sel (native_string_lit "@Tuple") tupleDD native_nat_zero (native_int_to_nat n) ≠
                    SmtType.None := by
                rw [← hSmt]
                exact hNonNone
              have hYN : y = Term.Numeral n :=
                eo_to_smt_eq_numeral y n hIdx
              subst y
              have hXTyNN : __eo_to_smt_type (__eo_typeof x) ≠ SmtType.None := by
                rw [hTyFromIH]
                simp
              have hEo :
                  __eo_to_smt_type
                      (__eo_typeof
                        (Term.Apply (Term.UOp1 UserOp1.tuple_select (Term.Numeral n)) x)) =
                    __eo_to_smt_type
                      (__eo_list_nth (Term.UOp UserOp.Tuple) (__eo_typeof x)
                        (Term.Numeral n)) := by
                exact
                  eo_to_smt_type_typeof_apply_apply_tuple_select_of_int
                    (Term.Numeral n) x (__eo_typeof x) rfl rfl hXTyNN
              rw [hSmt, hEo]
              have hList :
                  __eo_is_list (Term.UOp UserOp.Tuple) (__eo_typeof x) =
                    Term.Boolean true :=
                eo_tuple_is_list_true_of_smt_tuple_type hTyBody
              have hTupleWf :
                  __smtx_type_wf (SmtType.Datatype (native_string_lit "@Tuple") tupleDD) = true :=
                Smtm.smt_datatype_wf_of_non_none_type
                  (__eo_to_smt x) (native_string_lit "@Tuple") tupleDD hArgTy
              have hXValidTop : eo_type_valid (__eo_typeof x) :=
                eo_type_valid_of_smt_wf (__eo_typeof x) (by
                  simpa [hTyFromIH] using hTupleWf)
              have hXValidRec : eo_type_valid_rec [] (__eo_typeof x) :=
                eo_type_valid_rec_of_tuple_smt_type hTyBody hXValidTop
              simp [__eo_list_nth, __eo_requires, hList, native_ite, native_teq,
                native_not, SmtEval.native_not]
              have hnNonneg : (0 : Int) ≤ n := by
                simpa [native_zleq, SmtEval.native_zleq] using hNonneg
              have hNatInt :
                  native_nat_to_int (native_int_to_nat n) = n := by
                simp [native_nat_to_int, native_int_to_nat,
                  Smtm.native_nat_to_int, SmtEval.native_int_to_nat,
                  Int.toNat_of_nonneg hnNonneg]
              simpa [hNatInt] using
                smtx_ret_typeof_tuple_sel_eq_eo_list_nth_rec_nat
                  (T := __eo_typeof x) (d := body) (j := native_int_to_nat n)
                  hTyBody hXValidRec
        | _ =>
            exact eo_to_smt_typeof_matches_translation_of_smt_none
              (Term.Apply (Term.UOp1 UserOp1.tuple_select y) x)
              (by
                change
                  __smtx_typeof
                      (__eo_to_smt_tuple_select
                        (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y) (__eo_to_smt x)) =
                    SmtType.None
                rw [hTy, hIdx]
                simp [__eo_to_smt_tuple_select, __eo_to_smt_tuple_decl])
              hNonNone
      · exact eo_to_smt_typeof_matches_translation_of_smt_none
          (Term.Apply (Term.UOp1 UserOp1.tuple_select y) x)
          (by
            change
              __smtx_typeof
                  (__eo_to_smt_tuple_select
                    (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y) (__eo_to_smt x)) =
                SmtType.None
            rw [hTy]
            cases d with
            | nil =>
                cases __eo_to_smt y <;> simp [__eo_to_smt_tuple_select]
            | cons s2 body rest =>
                cases rest with
                | nil =>
                    cases __eo_to_smt y <;>
                      simp [__eo_to_smt_tuple_select, hTuple, native_streq,
                        native_and, native_ite]
                | cons s3 body3 rest3 =>
                    cases __eo_to_smt y <;> simp [__eo_to_smt_tuple_select])
          hNonNone
  | _ =>
      exact eo_to_smt_typeof_matches_translation_of_smt_none
        (Term.Apply (Term.UOp1 UserOp1.tuple_select y) x)
        (by
          change
            __smtx_typeof
                (__eo_to_smt_tuple_select
                  (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y) (__eo_to_smt x)) =
              SmtType.None
          rw [hTy]
          simp [__eo_to_smt_tuple_select])
        hNonNone

private theorem smtx_tuple_head_wf_component_of_wf
    (T : SmtType) (c : SmtDatatypeCons)
    (hNotTupleRef : T ≠ SmtType.TypeRef (native_string_lit "@Tuple"))
    (hWf :
      __smtx_type_wf
          (SmtType.Datatype (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl
              (SmtDatatype.sum (SmtDatatypeCons.cons T c) SmtDatatype.null))) =
        true) :
    __smtx_type_wf_component T = true := by
  have hOuterComp :
      __smtx_type_wf_component
          (SmtType.Datatype (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl
              (SmtDatatype.sum (SmtDatatypeCons.cons T c) SmtDatatype.null))) =
        true := by
    simpa [__smtx_type_wf] using hWf
  have hOuterRec := (Smtm.smtx_type_wf_component_parts hOuterComp).2
  have hCons :
      __smtx_dt_cons_wf_rec
          (__eo_to_smt_tuple_decl
            (SmtDatatype.sum (SmtDatatypeCons.cons T c) SmtDatatype.null))
          (SmtDatatypeCons.cons T c) = true := by
    have hOuterRec' := hOuterRec
    simp [__smtx_type_wf_rec, __eo_to_smt_tuple_decl,
      __smtx_decl_wf_rec, __smtx_dt_wf_rec, __smtx_dd_has_dt,
      native_streq, SmtEval.native_streq, native_and, native_or,
      native_not] at hOuterRec'
    exact hOuterRec'.1
  cases hT : T with
  | TypeRef s =>
      by_cases hs : s = native_string_lit "@Tuple"
      · subst s
        exact False.elim (hNotTupleRef hT)
      · simp [__smtx_dt_cons_wf_rec, __eo_to_smt_tuple_decl,
          __smtx_dd_has_dt, hT, hs, native_streq, SmtEval.native_streq,
          native_and, native_or] at hCons
  | _ =>
      rw [hT] at hCons
      simp only [__smtx_dt_cons_wf_rec, native_and, Bool.and_eq_true] at hCons
      exact Smtm.smtx_type_wf_component_of_parts hCons.1.1 hCons.1.2

/-- Localizes the remaining tuple-constructor recovery obligation. -/
private theorem eo_to_smt_typeof_matches_translation_apply_tuple_of_tail_type
    (x y : Term) (c : SmtDatatypeCons)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hTailTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl (SmtDatatype.sum c SmtDatatype.null)))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) y) x)) ≠
        SmtType.None) :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) y) x)) =
        __eo_to_smt_type
          (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) y) x)) := by
  let headTy := __smtx_typeof (__eo_to_smt y)
  let tailD := SmtDatatype.sum c SmtDatatype.null
  let fullD := SmtDatatype.sum (SmtDatatypeCons.cons headTy c) SmtDatatype.null
  let tailDD := __eo_to_smt_tuple_decl tailD
  let fullDD := __eo_to_smt_tuple_decl fullD
  have hPrependNN :
      __smtx_typeof
          (__eo_to_smt_tuple_prepend (__eo_to_smt y) headTy (__eo_to_smt x)) ≠
        SmtType.None := by
    change
      __smtx_typeof
          (__eo_to_smt_tuple_prepend (__eo_to_smt y) headTy (__eo_to_smt x)) ≠
        SmtType.None at hNonNone
    exact hNonNone
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) y) x)) =
        SmtType.Datatype (native_string_lit "@Tuple") fullDD := by
    change
      __smtx_typeof
          (__eo_to_smt_tuple_prepend (__eo_to_smt y) headTy (__eo_to_smt x)) =
        SmtType.Datatype (native_string_lit "@Tuple") fullDD
    exact
      smtx_tuple_prepend_typeof_of_tail_tuple_type
        (__eo_to_smt x) (__eo_to_smt y) headTy c
        (by simpa [tailD] using hTailTy) hPrependNN
  have hYNN : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None :=
    smtx_tuple_prepend_head_non_none_of_tail_tuple_type
      (__eo_to_smt x) (__eo_to_smt y) headTy c
      (by simpa [tailD] using hTailTy) hPrependNN
  have hYEq := ihY hYNN
  have hYTypeNN : __eo_to_smt_type (__eo_typeof y) ≠ SmtType.None := by
    rw [← hYEq]
    exact hYNN
  have hYNotStuck : __eo_typeof y ≠ Term.Stuck :=
    eo_term_ne_stuck_of_smt_type_non_none (__eo_typeof y) hYTypeNN
  have hXNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hTailTy]
    simp
  have hXEq := ihX hXNN
  have hXTailType :
      __eo_to_smt_type (__eo_typeof x) =
        SmtType.Datatype (native_string_lit "@Tuple") tailDD := by
    exact hXEq.symm.trans (by simpa [tailDD, tailD] using hTailTy)
  have hXTypeNN : __eo_to_smt_type (__eo_typeof x) ≠ SmtType.None := by
    rw [hXTailType]
    simp
  have hXNotStuck : __eo_typeof x ≠ Term.Stuck :=
    eo_term_ne_stuck_of_smt_type_non_none (__eo_typeof x) hXTypeNN
  have hXTailLenOk :
      __eo_is_ok (__eo_list_len (Term.UOp UserOp.Tuple) (__eo_typeof x)) =
        Term.Boolean true :=
    eo_tuple_list_len_ok_of_smt_tuple_type hXTailType
  have hFullWfForRaw :
      __smtx_type_wf
          (SmtType.Datatype (native_string_lit "@Tuple") fullDD) = true :=
    Smtm.smt_datatype_wf_of_non_none_type
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) y) x))
      (native_string_lit "@Tuple") fullDD hSmt
  have hHeadNotTupleRef :
      headTy ≠ SmtType.TypeRef (native_string_lit "@Tuple") := by
    intro hRef
    apply eo_to_smt_type_ne_tuple_typeref (__eo_typeof y)
    rw [← hYEq]
    exact hRef
  have hHeadComp : __smtx_type_wf_component headTy = true :=
    smtx_tuple_head_wf_component_of_wf headTy c hHeadNotTupleRef
      (by simpa [fullDD, fullD] using hFullWfForRaw)
  have hHeadParts :
      native_inhabited_type headTy = true ∧ __smtx_type_wf_rec headTy = true :=
    Smtm.smtx_type_wf_component_parts hHeadComp
  have hRaw :
      __eo_to_smt_type_tuple headTy (__eo_to_smt_type (__eo_typeof x)) =
        SmtType.Datatype (native_string_lit "@Tuple") fullDD := by
    rw [hXTailType]
    simp [__eo_to_smt_type_tuple, __eo_to_smt_tuple_decl, tailDD,
      tailD, fullDD, fullD, native_streq, SmtEval.native_streq,
      hHeadParts.1, hHeadParts.2, native_and, native_ite]
  /- Obsolete substitution-based tuple head well-formedness extraction.
  have hRaw :
      __eo_to_smt_type_tuple headTy (__eo_to_smt_type (__eo_typeof x)) =
        SmtType.Datatype (native_string_lit "@Tuple") fullD := by
    have hFullWfFromRaw : __smtx_type_wf (SmtType.Datatype (native_string_lit "@Tuple") fullD) = true :=
      Smtm.smt_datatype_wf_of_non_none_type
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) y) x))
        (native_string_lit "@Tuple") fullD hSmt
    have hHeadNA : __smtx_type_no_alias_rec native_reflist_nil headTy = true :=
      Smtm.tuple_head_no_alias_of_type_wf (by simpa [fullD] using hFullWfFromRaw)
    have hHeadComp : __smtx_type_wf_component headTy = true := by
      have hUnfold : headTy = __smtx_typeof (__eo_to_smt y) := rfl
      have hCompFull :
          __smtx_type_wf_component (SmtType.Datatype (native_string_lit "@Tuple") fullD) = true := by
        simp only [__smtx_type_wf] at hFullWfFromRaw
        exact hFullWfFromRaw
      have hRecFull :
          __smtx_type_wf_rec (SmtType.Datatype (native_string_lit "@Tuple") fullD)
              (SmtType.Datatype (native_string_lit "@Tuple") fullD) = true :=
        (Smtm.smtx_type_wf_component_parts hCompFull).2
      have hDtWf :
          __smtx_dt_wf_rec
              (__smtx_dt_substitute (native_string_lit "@Tuple") fullD fullD) fullD = true := by
        simp only [__smtx_type_wf_rec] at hRecFull
        exact hRecFull
      have hConsWf :
          __smtx_dt_cons_wf_rec
              (SmtDatatypeCons.cons
                (__smtx_type_substitute (native_string_lit "@Tuple") fullD headTy)
                (__smtx_dtc_substitute (native_string_lit "@Tuple") fullD c))
              (SmtDatatypeCons.cons headTy c) = true := by
        have hDtWf' := hDtWf
        simp only [fullD, __smtx_dt_substitute, __smtx_dtc_substitute, __smtx_dt_wf_rec] at hDtWf'
        cases hb :
            __smtx_dt_cons_wf_rec
              (SmtDatatypeCons.cons
                (__smtx_type_substitute (native_string_lit "@Tuple") fullD headTy)
                (__smtx_dtc_substitute (native_string_lit "@Tuple") fullD c))
              (SmtDatatypeCons.cons headTy c) with
        | true => rfl
        | false => rw [hb] at hDtWf'; simp [native_ite] at hDtWf'
      have hRes : __eo_reserved_datatype_name (native_string_lit "@Tuple") = true := by
        native_decide
      have hNoOp :
          __smtx_type_substitute (native_string_lit "@Tuple") fullD headTy = headTy := by
        rw [hUnfold]
        cases hshape : __smtx_typeof (__eo_to_smt y) with
        | Datatype s2 d2 =>
            by_cases hs2 : native_streq (native_string_lit "@Tuple") s2 = true
            · simp [__smtx_type_substitute, native_ite, hs2]
            · have hs2F : native_streq (native_string_lit "@Tuple") s2 = false :=
                Bool.eq_false_iff.mpr hs2
              have hFree :
                  hasFreeTy (native_string_lit "@Tuple") native_reflist_nil
                    (__smtx_typeof (__eo_to_smt y)) = false := by
                rw [hYEq]
                exact hasFreeTy_reserved_of_translate (native_string_lit "@Tuple") hRes
                  (__eo_typeof y) native_reflist_nil
              have hFreeDt :
                  hasFreeDt (native_string_lit "@Tuple")
                    (native_reflist_insert native_reflist_nil s2) d2 = false := by
                have hFree' := hFree
                rw [hshape] at hFree'
                simpa [hasFreeTy] using hFree'
              have hNotMem :
                  native_reflist_contains (native_reflist_insert native_reflist_nil s2)
                      (native_string_lit "@Tuple") = false := by
                simp only [native_reflist_contains, native_reflist_insert, List.mem_cons,
                  decide_eq_false_iff_not]
                rintro (hEq | hEq)
                · have hTrue : native_streq (native_string_lit "@Tuple") s2 = true := by
                    simp [native_streq, hEq]
                  rw [hTrue] at hs2F
                  exact absurd hs2F (by decide)
                · simp [native_reflist_nil] at hEq
              have hDtNoOp :
                  __smtx_dt_substitute (native_string_lit "@Tuple")
                      (__smtx_dt_lift s2 d2 fullD) d2 = d2 :=
                Smtm.subst_noop_no_free_dt (native_string_lit "@Tuple") d2
                  (__smtx_dt_lift s2 d2 fullD)
                  (native_reflist_insert native_reflist_nil s2) hNotMem hFreeDt
              simp [__smtx_type_substitute, native_ite, hs2F, hDtNoOp]
        | TypeRef sU =>
            exfalso
            have hNeTuple :
                __eo_to_smt_type (__eo_typeof y) ≠
                  SmtType.TypeRef (native_string_lit "@Tuple") :=
              eo_to_smt_type_ne_tuple_typeref (__eo_typeof y)
            rw [← hYEq, hshape] at hNeTuple
            have hsUne : native_streq (native_string_lit "@Tuple") sU = false := by
              cases h : native_streq (native_string_lit "@Tuple") sU
              · rfl
              · exfalso
                apply hNeTuple
                congr 1
                exact (show native_string_lit "@Tuple" = sU by simpa [native_streq] using h).symm
            rw [hUnfold, hshape] at hConsWf
            simp [__smtx_type_substitute, native_ite, hsUne, __smtx_dt_cons_wf_rec,
              __smtx_type_wf_rec, native_and] at hConsWf
        | Seq A => simp [__smtx_type_substitute]
        | Set A => simp [__smtx_type_substitute]
        | Map A B => simp [__smtx_type_substitute]
        | FunType A B => simp [__smtx_type_substitute]
        | DtcAppType A B => simp [__smtx_type_substitute]
        | None => simp [__smtx_type_substitute]
        | RegLan => simp [__smtx_type_substitute]
        | Bool => simp [__smtx_type_substitute]
        | Int => simp [__smtx_type_substitute]
        | Real => simp [__smtx_type_substitute]
        | BitVec n => simp [__smtx_type_substitute]
        | Char => simp [__smtx_type_substitute]
        | USort i => simp [__smtx_type_substitute]
      rw [hNoOp] at hConsWf
      have hNotRef : ∀ s, headTy ≠ SmtType.TypeRef s := by
        intro s hEq
        rw [hEq] at hConsWf
        simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite, native_and] at hConsWf
      have hgen :
          __smtx_dt_cons_wf_rec
              (SmtDatatypeCons.cons headTy
                (__smtx_dtc_substitute (native_string_lit "@Tuple") fullD c))
              (SmtDatatypeCons.cons headTy c) =
            native_ite
              (native_and (native_inhabited_type headTy) (__smtx_type_wf_rec headTy headTy))
              (__smtx_dt_cons_wf_rec
                (__smtx_dtc_substitute (native_string_lit "@Tuple") fullD c) c)
              false := by
        cases hHT : headTy with
        | TypeRef s => exact absurd hHT (hNotRef s)
        | _ => simp [__smtx_dt_cons_wf_rec]
      rw [hgen] at hConsWf
      cases hb :
          native_and (native_inhabited_type headTy) (__smtx_type_wf_rec headTy headTy) with
      | false => rw [hb] at hConsWf; exact absurd hConsWf (by simp [native_ite])
      | true =>
          simp only [native_and, Bool.and_eq_true] at hb
          exact Smtm.smtx_type_wf_component_of_parts hb.1 hb.2 hHeadNA
    have hHeadParts :
        native_inhabited_type headTy = true ∧
          __smtx_type_wf_rec headTy headTy = true :=
      Smtm.smtx_type_wf_component_parts hHeadComp
    simp [headTy, tailD, fullD, hXTailType, __eo_to_smt_type_tuple,
      __smtx_type_wf_component, hHeadParts.1, hHeadParts.2, hHeadNA,
      native_streq, native_and, native_ite]
  -/
  have hFullWf : __smtx_type_wf (SmtType.Datatype (native_string_lit "@Tuple") fullDD) = true :=
    Smtm.smt_datatype_wf_of_non_none_type
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) y) x))
      (native_string_lit "@Tuple") fullDD hSmt
  have hRawWf :
      __smtx_type_wf
          (__eo_to_smt_type_tuple headTy (__eo_to_smt_type (__eo_typeof x))) =
        true := by
    simpa [hRaw] using hFullWf
  have hEo :
      __eo_to_smt_type
          (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) y) x)) =
        SmtType.Datatype (native_string_lit "@Tuple") fullDD := by
    change
      __eo_to_smt_type (__eo_typeof_tuple (__eo_typeof y) (__eo_typeof x)) =
        SmtType.Datatype (native_string_lit "@Tuple") fullDD
    rw [__eo_typeof_tuple.eq_def]
    simp [__eo_requires, hXTailLenOk, native_ite,
      native_teq, native_not, SmtEval.native_not]
    rw [← hYEq]
    simp [headTy, hRaw, hFullWf]
  exact hSmt.trans hEo.symm

/-- A non-`none` tuple prepend has a fully typed tuple tail. -/
theorem eo_to_smt_tuple_tail_type_of_non_none_from_checked
    (x y : Term)
      (hNonNone :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) y) x)) ≠
          SmtType.None) :
      ∃ c,
        __smtx_typeof (__eo_to_smt x) =
          SmtType.Datatype (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl (SmtDatatype.sum c SmtDatatype.null)) := by
  let headTy := __smtx_typeof (__eo_to_smt y)
  have hPrependNN :
      __smtx_typeof
          (__eo_to_smt_tuple_prepend (__eo_to_smt y) headTy (__eo_to_smt x)) ≠
        SmtType.None := by
    change
      __smtx_typeof
          (__eo_to_smt_tuple_prepend (__eo_to_smt y) headTy (__eo_to_smt x)) ≠
        SmtType.None at hNonNone
    exact hNonNone
  unfold __eo_to_smt_tuple_prepend at hPrependNN
  cases hTail : __smtx_typeof (__eo_to_smt x) with
  | Datatype s dd =>
      cases dd with
      | nil =>
          exact False.elim (hPrependNN (by
            simp [hTail, __eo_to_smt_tuple_prepend_of_type]))
      | cons s2 body restDecl =>
          cases restDecl with
          | cons s3 body3 rest3 =>
              exact False.elim (hPrependNN (by
                simp [hTail, __eo_to_smt_tuple_prepend_of_type]))
          | nil =>
              cases body with
              | null =>
                  exact False.elim (hPrependNN (by
                    simp [hTail, __eo_to_smt_tuple_prepend_of_type]))
              | sum c restBody =>
                  cases restBody with
                  | sum cRest dRest =>
                      exact False.elim (hPrependNN (by
                        simp [hTail, __eo_to_smt_tuple_prepend_of_type]))
                  | null =>
                      by_cases hs : s = native_string_lit "@Tuple"
                      · subst s
                        by_cases hs2 : s2 = native_string_lit "@Tuple"
                        · subst s2
                          exact ⟨c, by
                            simp [__eo_to_smt_tuple_decl] at hTail ⊢⟩
                        · exact False.elim (hPrependNN (by
                            simp [hTail, __eo_to_smt_tuple_prepend_of_type,
                              hs2, native_streq, native_and, native_ite]))
                      · exact False.elim (hPrependNN (by
                          simp [hTail, __eo_to_smt_tuple_prepend_of_type,
                            hs, native_streq, native_and, native_ite]))
  | _ =>
      exact False.elim (hPrependNN (by
        simp [hTail, __eo_to_smt_tuple_prepend_of_type]))

private theorem eo_to_smt_typeof_matches_translation_apply_tuple_from_valid_ih
    (x y : Term)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y) ∧
        eo_type_valid (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) ∧
          eo_type_valid (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) y) x)) := by
  rcases eo_to_smt_tuple_tail_type_of_non_none_from_checked
      x y hNonNone with ⟨c, hTailTy⟩
  exact
    eo_to_smt_typeof_matches_translation_apply_tuple_of_tail_type
      x y c (fun hYNN => (ihY hYNN).1) (fun hXNN => (ihX hXNN).1)
        hTailTy hNonNone

private theorem eo_to_smt_typeof_matches_translation_apply_tuple
    (x y : Term)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y) ∧
        eo_type_valid (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) ∧
        eo_type_valid (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) y) x)) := by
  exact
    eo_to_smt_typeof_matches_translation_apply_tuple_from_valid_ih
      x y ihY ihX hNonNone

/-- Simplifies EO-to-SMT translation for map `select`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_select
    (x y : Term)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.select) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.select) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.select) y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.select) y) x) =
        SmtTerm.select (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hApplyNN :
      term_has_non_none_type (SmtTerm.select (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases select_args_of_non_none hApplyNN with ⟨A, B, hY, hX⟩
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.select) y) x)) =
        B := by
    rw [hTranslate, typeof_select_eq (__eo_to_smt y) (__eo_to_smt x)]
    simp [__smtx_typeof_select, native_ite, native_Teq, hY, hX]
  have hComps :=
    smtx_map_components_field_wf_rec_of_non_none_type_apply (__eo_to_smt y) A B hY
  have hANN : A ≠ SmtType.None :=
    smtx_type_field_wf_rec_ne_none hComps.1
  rcases eo_typeof_eq_map_of_smt_map_from_ih y ihY hY with
    ⟨U, T, hYArray, hU, hT⟩
  have hXTrans : __eo_to_smt_type (__eo_typeof x) = A := by
    have hXNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hX]
      exact hANN
    rw [← ihX hXNN]
    exact hX
  have hXU : __eo_typeof x = U :=
    eo_to_smt_type_injective_of_field_wf_rec hXTrans hU hComps.1
  have hUNN : __eo_to_smt_type U ≠ SmtType.None := by
    rw [hU]
    exact hANN
  have hEo :
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.select) y) x)) =
        B := by
    rw [← hT]
    exact eo_to_smt_type_typeof_apply_apply_select_of_array x y U T hYArray hXU hUNN
  exact hSmt.trans hEo.symm

/-- `eq` application, using the operand SMT type injectivity invariant. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_eq_from_valid_ih_field_wf
    (y x : Term)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y) ∧
          eo_type_valid (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x)) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x)) ≠
      SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x)) := by
  intro hNonNone
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x) =
        SmtTerm.eq (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hEqNN :
      __smtx_typeof_eq
          (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x)) ≠
        SmtType.None := by
    intro hNone
    apply hNonNone
    rw [hTranslate, typeof_eq_eq]
    exact hNone
  rcases smtx_typeof_eq_non_none hEqNN with ⟨hSame, hYNN⟩
  let T := __smtx_typeof (__eo_to_smt y)
  have hY : __smtx_typeof (__eo_to_smt y) = T := rfl
  have hX : __smtx_typeof (__eo_to_smt x) = T := hSame.symm
  have hXNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hX]
    exact hYNN
  have hYTrans : __eo_to_smt_type (__eo_typeof y) = T :=
    (ihY hYNN).1.symm.trans hY
  have hXTrans : __eo_to_smt_type (__eo_typeof x) = T :=
    (ihX hXNN).symm.trans hX
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x)) =
        SmtType.Bool := by
    rw [hTranslate, typeof_eq_eq, hY, hX]
    simpa [__smtx_typeof_eq, native_ite, native_Teq] using
      smtx_typeof_guard_of_non_none T SmtType.Bool hYNN
  have hYTypeNN : __eo_to_smt_type (__eo_typeof y) ≠ SmtType.None := by
    intro hNone
    exact hYNN (hY.trans (hYTrans.symm.trans hNone))
  have hEo :
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x)) =
        SmtType.Bool := by
    cases hT : T with
    | None =>
        exact False.elim (hYNN (hY.trans hT))
    | Bool =>
        have hXB : __eo_to_smt_type (__eo_typeof x) = SmtType.Bool := hXTrans.trans hT
        have hYB : __eo_to_smt_type (__eo_typeof y) = SmtType.Bool := hYTrans.trans hT
        have hEqEo : __eo_typeof x = __eo_typeof y := by
          rw [eo_to_smt_type_eq_bool hXB, eo_to_smt_type_eq_bool hYB]
        exact eo_to_smt_type_typeof_apply_apply_eq_of_same_type
          x y (__eo_typeof y) rfl hEqEo hYTypeNN
    | Int =>
        have hXI : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := hXTrans.trans hT
        have hYI : __eo_to_smt_type (__eo_typeof y) = SmtType.Int := hYTrans.trans hT
        have hEqEo : __eo_typeof x = __eo_typeof y := by
          rw [eo_to_smt_type_eq_int hXI, eo_to_smt_type_eq_int hYI]
        exact eo_to_smt_type_typeof_apply_apply_eq_of_same_type
          x y (__eo_typeof y) rfl hEqEo hYTypeNN
    | Real =>
        have hXR : __eo_to_smt_type (__eo_typeof x) = SmtType.Real := hXTrans.trans hT
        have hYR : __eo_to_smt_type (__eo_typeof y) = SmtType.Real := hYTrans.trans hT
        have hEqEo : __eo_typeof x = __eo_typeof y := by
          rw [eo_to_smt_type_eq_real hXR, eo_to_smt_type_eq_real hYR]
        exact eo_to_smt_type_typeof_apply_apply_eq_of_same_type
          x y (__eo_typeof y) rfl hEqEo hYTypeNN
    | RegLan =>
        have hXR : __eo_to_smt_type (__eo_typeof x) = SmtType.RegLan := hXTrans.trans hT
        have hYR : __eo_to_smt_type (__eo_typeof y) = SmtType.RegLan := hYTrans.trans hT
        have hEqEo : __eo_typeof x = __eo_typeof y := by
          rw [eo_to_smt_type_eq_reglan hXR, eo_to_smt_type_eq_reglan hYR]
        exact eo_to_smt_type_typeof_apply_apply_eq_of_same_type
          x y (__eo_typeof y) rfl hEqEo hYTypeNN
    | BitVec w =>
        have hXB : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w := hXTrans.trans hT
        have hYB : __eo_to_smt_type (__eo_typeof y) = SmtType.BitVec w := hYTrans.trans hT
        have hEqEo : __eo_typeof x = __eo_typeof y := by
          rw [eo_to_smt_type_eq_bitvec hXB, eo_to_smt_type_eq_bitvec hYB]
        exact eo_to_smt_type_typeof_apply_apply_eq_of_same_type
          x y (__eo_typeof y) rfl hEqEo hYTypeNN
    | Map A B =>
        have hYM : __eo_to_smt_type (__eo_typeof y) = SmtType.Map A B := hYTrans.trans hT
        have hXM : __eo_to_smt_type (__eo_typeof x) = SmtType.Map A B := hXTrans.trans hT
        rcases eo_to_smt_type_eq_map hYM with ⟨Y1, Y2, hYEo, hY1, hY2⟩
        rcases eo_to_smt_type_eq_map hXM with ⟨X1, X2, hXEo, hX1, hX2⟩
        have hComps :=
          smtx_map_components_field_wf_rec_of_non_none_type_apply
            (__eo_to_smt y) A B (hY.trans hT)
        have h1 : X1 = Y1 :=
          eo_to_smt_type_injective_of_field_wf_rec hX1 hY1 hComps.1
        have h2 : X2 = Y2 :=
          eo_to_smt_type_injective_of_field_wf_rec hX2 hY2 hComps.2
        have hEqEo : __eo_typeof x = __eo_typeof y := by
          rw [hXEo, hYEo, h1, h2]
        exact eo_to_smt_type_typeof_apply_apply_eq_of_same_type
          x y (__eo_typeof y) rfl hEqEo hYTypeNN
    | Set A =>
        have hYS : __eo_to_smt_type (__eo_typeof y) = SmtType.Set A := hYTrans.trans hT
        have hXS : __eo_to_smt_type (__eo_typeof x) = SmtType.Set A := hXTrans.trans hT
        rcases eo_to_smt_type_eq_set hYS with ⟨Y0, hYEo, hY0⟩
        rcases eo_to_smt_type_eq_set hXS with ⟨X0, hXEo, hX0⟩
        have hWF :=
          smtx_set_component_field_wf_rec_of_non_none_type_apply
            (__eo_to_smt y) A (hY.trans hT)
        have h0 : X0 = Y0 :=
          eo_to_smt_type_injective_of_field_wf_rec hX0 hY0 hWF
        have hEqEo : __eo_typeof x = __eo_typeof y := by
          rw [hXEo, hYEo, h0]
        exact eo_to_smt_type_typeof_apply_apply_eq_of_same_type
          x y (__eo_typeof y) rfl hEqEo hYTypeNN
    | Seq A =>
        have hYS : __eo_to_smt_type (__eo_typeof y) = SmtType.Seq A := hYTrans.trans hT
        have hXS : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq A := hXTrans.trans hT
        rcases eo_to_smt_type_eq_seq hYS with ⟨Y0, hYEo, hY0⟩
        rcases eo_to_smt_type_eq_seq hXS with ⟨X0, hXEo, hX0⟩
        have hWF :=
          smtx_seq_component_field_wf_rec_of_non_none_type_apply
            (__eo_to_smt y) A (hY.trans hT)
        have h0 : X0 = Y0 :=
          eo_to_smt_type_injective_of_field_wf_rec hX0 hY0 hWF
        have hEqEo : __eo_typeof x = __eo_typeof y := by
          rw [hXEo, hYEo, h0]
        exact eo_to_smt_type_typeof_apply_apply_eq_of_same_type
          x y (__eo_typeof y) rfl hEqEo hYTypeNN
    | Char =>
        have hXC : __eo_to_smt_type (__eo_typeof x) = SmtType.Char := hXTrans.trans hT
        have hYC : __eo_to_smt_type (__eo_typeof y) = SmtType.Char := hYTrans.trans hT
        have hEqEo : __eo_typeof x = __eo_typeof y := by
          rw [eo_to_smt_type_eq_char hXC, eo_to_smt_type_eq_char hYC]
        exact eo_to_smt_type_typeof_apply_apply_eq_of_same_type
          x y (__eo_typeof y) rfl hEqEo hYTypeNN
    | Datatype s d =>
        have hYD : __eo_to_smt_type (__eo_typeof y) = SmtType.Datatype s d := hYTrans.trans hT
        have hXD : __eo_to_smt_type (__eo_typeof x) = SmtType.Datatype s d := hXTrans.trans hT
        have hWF :=
          smtx_datatype_field_wf_rec_of_non_none_type_apply
            (__eo_to_smt y) s d (hY.trans hT)
        have hEqEo : __eo_typeof x = __eo_typeof y :=
          eo_to_smt_type_injective_of_field_wf_rec hXD hYD hWF
        exact eo_to_smt_type_typeof_apply_apply_eq_of_same_type
          x y (__eo_typeof y) rfl hEqEo hYTypeNN
    | TypeRef s =>
        have hXT : __eo_to_smt_type (__eo_typeof x) = SmtType.TypeRef s := hXTrans.trans hT
        have hYT : __eo_to_smt_type (__eo_typeof y) = SmtType.TypeRef s := hYTrans.trans hT
        have hEqEo : __eo_typeof x = __eo_typeof y := by
          rw [eo_to_smt_type_eq_typeref hXT, eo_to_smt_type_eq_typeref hYT]
        exact eo_to_smt_type_typeof_apply_apply_eq_of_same_type
          x y (__eo_typeof y) rfl hEqEo hYTypeNN
    | USort i =>
        have hXU : __eo_to_smt_type (__eo_typeof x) = SmtType.USort i := hXTrans.trans hT
        have hYU : __eo_to_smt_type (__eo_typeof y) = SmtType.USort i := hYTrans.trans hT
        have hEqEo : __eo_typeof x = __eo_typeof y := by
          rw [eo_to_smt_type_eq_usort hXU, eo_to_smt_type_eq_usort hYU]
        exact eo_to_smt_type_typeof_apply_apply_eq_of_same_type
          x y (__eo_typeof y) rfl hEqEo hYTypeNN
    | FunType A B =>
        have hYF : __eo_to_smt_type (__eo_typeof y) = SmtType.FunType A B := hYTrans.trans hT
        have hXF : __eo_to_smt_type (__eo_typeof x) = SmtType.FunType A B := hXTrans.trans hT
        rcases eo_to_smt_type_eq_fun hYF with ⟨Y1, Y2, hYEo, hY1, hY2⟩
        rcases eo_to_smt_type_eq_fun hXF with ⟨X1, X2, hXEo, hX1, hX2⟩
        have hComps :=
          smtx_fun_components_field_wf_rec_of_non_none_type_apply
            (__eo_to_smt y) A B (hY.trans hT)
        have h1 : X1 = Y1 :=
          eo_to_smt_type_injective_of_field_wf_rec hX1 hY1 hComps.1
        have h2 : X2 = Y2 :=
          eo_to_smt_type_injective_of_wf hX2 hY2 hComps.2
        have hEqEo : __eo_typeof x = __eo_typeof y := by
          rw [hXEo, hYEo, h1, h2]
        exact eo_to_smt_type_typeof_apply_apply_eq_of_same_type
          x y (__eo_typeof y) rfl hEqEo hYTypeNN
    | DtcAppType A B =>
        have hYD : __eo_to_smt_type (__eo_typeof y) = SmtType.DtcAppType A B :=
          hYTrans.trans hT
        have hXD : __eo_to_smt_type (__eo_typeof x) = SmtType.DtcAppType A B :=
          hXTrans.trans hT
        rcases eo_to_smt_type_eq_dtc_app hYD with ⟨Y1, Y2, hYEo, hY1, hY2⟩
        rcases eo_to_smt_type_eq_dtc_app hXD with ⟨X1, X2, hXEo, hX1, hX2⟩
        have hYValidTop : eo_type_valid (__eo_typeof y) :=
          (ihY hYNN).2
        have hYValidDtc : eo_type_valid_rec [] (Term.DtcAppType Y1 Y2) := by
          have hYValidTop' := hYValidTop
          rw [hYEo] at hYValidTop'
          simpa [eo_type_valid, eo_type_valid_rec] using hYValidTop'
        have hYDtcTrans :
            __eo_to_smt_type (Term.DtcAppType Y1 Y2) = SmtType.DtcAppType A B := by
          simpa [hYEo] using hYD
        have hXDtcTrans :
            __eo_to_smt_type (Term.DtcAppType X1 X2) = SmtType.DtcAppType A B := by
          simpa [hXEo] using hXD
        have hEqDtc : Term.DtcAppType Y1 Y2 = Term.DtcAppType X1 X2 := by
          apply eo_to_smt_type_eq_of_valid_rec hYValidDtc
          exact hYDtcTrans.trans hXDtcTrans.symm
        have hEqEo : __eo_typeof x = __eo_typeof y := by
          rw [hXEo, hYEo]
          exact hEqDtc.symm
        exact eo_to_smt_type_typeof_apply_apply_eq_of_same_type
          x y (__eo_typeof y) rfl hEqEo hYTypeNN
  exact hSmt.trans hEo.symm

private theorem eo_to_smt_typeof_matches_translation_apply_apply_eq_from_ih_field_wf
    (y x : Term)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y) ∧
        eo_type_valid (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x)) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x)) ≠
      SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x)) := by
  exact
    eo_to_smt_typeof_matches_translation_apply_apply_eq_from_valid_ih_field_wf
      y x ihY ihX

/-- Closes binary `UOp` branches whose translated head is `none`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_none_head
    (op : UserOp) (y x : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) y) x) =
        SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt y)) (__eo_to_smt x)) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) y) x)) ≠
      SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp op) y) x)) := by
  exact eo_to_smt_typeof_matches_translation_of_smt_none
    (Term.Apply (Term.Apply (Term.UOp op) y) x)
    (by
      rw [hTranslate]
      exact typeof_apply_apply_none_head_eq (__eo_to_smt y) (__eo_to_smt x))

/-- Closes ternary `UOp` branches whose translated head starts from `none`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_none_head
    (op : UserOp) (z y x : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x) =
        SmtTerm.Apply
          (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt z)) (__eo_to_smt y))
          (__eo_to_smt x)) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) ≠
      SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) := by
  exact eo_to_smt_typeof_matches_translation_of_smt_none
    (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)
    (by
      rw [hTranslate]
      exact typeof_apply_apply_apply_none_head_eq
        (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x))

/-- Closes quaternary `UOp` branches whose translated head starts from `none`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_apply_none_head
    (op : UserOp) (w z y x : Term)
    (hTranslate :
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) w) z) y) x) =
        SmtTerm.Apply
          (SmtTerm.Apply
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt w)) (__eo_to_smt z))
            (__eo_to_smt y))
          (__eo_to_smt x)) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) w) z) y) x)) ≠
      SmtType.None ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) w) z) y) x)) =
      __eo_to_smt_type
        (__eo_typeof
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) w) z) y) x)) := by
  exact eo_to_smt_typeof_matches_translation_of_smt_none
    (Term.Apply (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) w) z) y) x)
    (by
      rw [hTranslate]
      exact typeof_apply_apply_apply_apply_none_head_eq
        (__eo_to_smt w) (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x))

private theorem bv_width_term_nonstuck (w : native_Nat) :
    Term.Numeral (native_nat_to_int w) ≠ Term.Stuck := by
  intro h
  cases h

/-- Dispatches direct-special binary heads shaped as `(UOp op) y`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_uop_application_head_obligation
    (op : UserOp) (y x : Term)
    (ihFAll :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp op) y)) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp op) y)) =
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp op) y)) ∧
        eo_type_valid (__eo_typeof (Term.Apply (Term.UOp op) y)))
    (ihYAll :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y) ∧
        eo_type_valid (__eo_typeof y))
    (ihXAll :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) ∧
        eo_type_valid (__eo_typeof x))
    (ihBelowAll :
      ∀ term,
        sizeOf term < sizeOf (Term.Apply (Term.Apply (Term.UOp op) y) x) ->
        __smtx_typeof (__eo_to_smt term) ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt term) = __eo_to_smt_type (__eo_typeof term) ∧
          eo_type_valid (__eo_typeof term)) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) y) x)) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp op) y) x)) := by
  intro hNonNone
  let ihF := fun hNN => (ihFAll hNN).1
  let ihY := fun hNN => (ihYAll hNN).1
  let ihX := fun hNN => (ihXAll hNN).1
  cases op
  case eq =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_eq_from_ih_field_wf
      y x ihYAll ihX hNonNone
  case distinct =>
    exfalso
    apply hNonNone
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.distinct) y) x) =
          SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.UOp UserOp.distinct) y)) (__eo_to_smt x) := by
      rfl
    rw [hTranslate]
    exact smtx_typeof_eo_to_smt_distinct_top_apply_eq_none y (__eo_to_smt x)
  case not =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_generic_of_head_from_ih
      UserOp.not y x (SmtTerm.not (__eo_to_smt y)) ihFAll ihXAll (by rfl)
      (by rfl) (by rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      hNonNone
  case to_real =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_generic_of_head_from_ih
      UserOp.to_real y x (SmtTerm.to_real (__eo_to_smt y)) ihFAll ihXAll (by rfl)
      (by rfl) (by rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      hNonNone
  case to_int =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_generic_of_head_from_ih
      UserOp.to_int y x (SmtTerm.to_int (__eo_to_smt y)) ihFAll ihXAll (by rfl)
      (by rfl) (by rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      hNonNone
  case is_int =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_generic_of_head_from_ih
      UserOp.is_int y x (SmtTerm.is_int (__eo_to_smt y)) ihFAll ihXAll (by rfl)
      (by rfl) (by rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      hNonNone
  case abs =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_generic_of_head_from_ih
      UserOp.abs y x (SmtTerm.abs (__eo_to_smt y)) ihFAll ihXAll (by rfl)
      (by rfl) (by rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      hNonNone
  case str_to_re =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_generic_of_head_from_ih
      UserOp.str_to_re y x (SmtTerm.str_to_re (__eo_to_smt y)) ihFAll ihXAll (by rfl)
      (by rfl) (by rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      hNonNone
  case re_mult =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_generic_of_head_from_ih
      UserOp.re_mult y x (SmtTerm.re_mult (__eo_to_smt y)) ihFAll ihXAll (by rfl)
      (by rfl) (by rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      hNonNone
  case re_plus =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_generic_of_head_from_ih
      UserOp.re_plus y x (SmtTerm.re_plus (__eo_to_smt y)) ihFAll ihXAll (by rfl)
      (by rfl) (by rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      hNonNone
  case re_opt =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_generic_of_head_from_ih
      UserOp.re_opt y x (SmtTerm.re_opt (__eo_to_smt y)) ihFAll ihXAll (by rfl)
      (by rfl) (by rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      hNonNone
  case re_comp =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_generic_of_head_from_ih
      UserOp.re_comp y x (SmtTerm.re_comp (__eo_to_smt y)) ihFAll ihXAll (by rfl)
      (by rfl) (by rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      hNonNone
  case set_singleton =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_generic_of_head_from_ih
      UserOp.set_singleton y x (SmtTerm.set_singleton (__eo_to_smt y)) ihFAll ihXAll (by rfl)
      (by rfl) (by rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      hNonNone
  case set_is_empty =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_generic_of_head_from_ih
      UserOp.set_is_empty y x
      (let _v0 := __eo_to_smt y
       SmtTerm.eq _v0
         (SmtTerm.set_empty (__eo_to_smt_set_elem_type (__smtx_typeof _v0)))) ihFAll ihXAll (by rfl)
      (by rfl) (by rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      hNonNone
  case set_is_singleton =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_generic_of_head_from_ih
      UserOp.set_is_singleton y x
      (let _v0 := __eo_to_smt y
       SmtTerm.eq _v0
         (SmtTerm.set_singleton
           (SmtTerm.map_diff _v0
             (SmtTerm.set_empty (__eo_to_smt_set_elem_type (__smtx_typeof _v0)))))) ihFAll ihXAll (by rfl)
      (by rfl) (by rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      hNonNone
  case str_contains =>
    exact eo_to_smt_typeof_matches_translation_apply_seq_ret_binop
      UserOp.str_contains SmtTerm.str_contains SmtType.Bool x y ihY ihX (by rfl)
      (typeof_str_contains_eq (__eo_to_smt y) (__eo_to_smt x))
      (fun {T} hy hx hT =>
        eo_to_smt_type_typeof_apply_apply_str_contains_of_seq x y T hy hx hT)
      hNonNone
  case str_prefixof =>
    exact eo_to_smt_typeof_matches_translation_apply_seq_ret_binop
      UserOp.str_prefixof SmtTerm.str_prefixof SmtType.Bool x y ihY ihX (by rfl)
      (typeof_str_prefixof_eq (__eo_to_smt y) (__eo_to_smt x))
      (fun {T} hy hx hT =>
        eo_to_smt_type_typeof_apply_apply_str_prefixof_of_seq x y T hy hx hT)
      hNonNone
  case str_suffixof =>
    exact eo_to_smt_typeof_matches_translation_apply_seq_ret_binop
      UserOp.str_suffixof SmtTerm.str_suffixof SmtType.Bool x y ihY ihX (by rfl)
      (typeof_str_suffixof_eq (__eo_to_smt y) (__eo_to_smt x))
      (fun {T} hy hx hT =>
        eo_to_smt_type_typeof_apply_apply_str_suffixof_of_seq x y T hy hx hT)
      hNonNone
  case str_lt =>
    exact eo_to_smt_typeof_matches_translation_apply_seq_char_binop
      UserOp.str_lt SmtTerm.str_lt SmtType.Bool x y (by rfl)
      (typeof_str_lt_eq (__eo_to_smt y) (__eo_to_smt x))
      (fun hy hx =>
        eo_to_smt_type_typeof_apply_apply_str_lt_of_seq_char x y
          (eo_typeof_eq_seq_char_of_smt_seq_char_from_ih y ihY hy)
          (eo_typeof_eq_seq_char_of_smt_seq_char_from_ih x ihX hx))
      hNonNone
  case str_leq =>
    exact eo_to_smt_typeof_matches_translation_apply_seq_char_binop
      UserOp.str_leq SmtTerm.str_leq SmtType.Bool x y (by rfl)
      (typeof_str_leq_eq (__eo_to_smt y) (__eo_to_smt x))
      (fun hy hx =>
        eo_to_smt_type_typeof_apply_apply_str_leq_of_seq_char x y
          (eo_typeof_eq_seq_char_of_smt_seq_char_from_ih y ihY hy)
          (eo_typeof_eq_seq_char_of_smt_seq_char_from_ih x ihX hx))
      hNonNone
  case str_concat =>
    exact eo_to_smt_typeof_matches_translation_apply_seq_binop
      UserOp.str_concat SmtTerm.str_concat x y ihY ihX (by rfl)
      (typeof_str_concat_eq (__eo_to_smt y) (__eo_to_smt x))
      (fun {T} hy hx hT =>
        eo_to_smt_type_typeof_apply_apply_str_concat_of_seq x y T hy hx hT)
      hNonNone
  case re_range =>
    exact eo_to_smt_typeof_matches_translation_apply_seq_char_binop
      UserOp.re_range SmtTerm.re_range SmtType.RegLan x y (by rfl)
      (typeof_re_range_eq (__eo_to_smt y) (__eo_to_smt x))
      (fun hy hx =>
        eo_to_smt_type_typeof_apply_apply_re_range_of_seq_char x y
          (eo_typeof_eq_seq_char_of_smt_seq_char_from_ih y ihY hy)
          (eo_typeof_eq_seq_char_of_smt_seq_char_from_ih x ihX hx))
      hNonNone
  case re_concat =>
    exact eo_to_smt_typeof_matches_translation_apply_reglan_binop
      UserOp.re_concat SmtTerm.re_concat x y (by rfl)
      (typeof_re_concat_eq (__eo_to_smt y) (__eo_to_smt x))
      (fun hy hx =>
        eo_to_smt_type_typeof_apply_apply_re_concat_of_reglan x y
          (eo_typeof_eq_reglan_of_smt_reglan_from_ih y ihY hy)
          (eo_typeof_eq_reglan_of_smt_reglan_from_ih x ihX hx))
      hNonNone
  case re_inter =>
    exact eo_to_smt_typeof_matches_translation_apply_reglan_binop
      UserOp.re_inter SmtTerm.re_inter x y (by rfl)
      (typeof_re_inter_eq (__eo_to_smt y) (__eo_to_smt x))
      (fun hy hx =>
        eo_to_smt_type_typeof_apply_apply_re_inter_of_reglan x y
          (eo_typeof_eq_reglan_of_smt_reglan_from_ih y ihY hy)
          (eo_typeof_eq_reglan_of_smt_reglan_from_ih x ihX hx))
      hNonNone
  case re_union =>
    exact eo_to_smt_typeof_matches_translation_apply_reglan_binop
      UserOp.re_union SmtTerm.re_union x y (by rfl)
      (typeof_re_union_eq (__eo_to_smt y) (__eo_to_smt x))
      (fun hy hx =>
        eo_to_smt_type_typeof_apply_apply_re_union_of_reglan x y
          (eo_typeof_eq_reglan_of_smt_reglan_from_ih y ihY hy)
          (eo_typeof_eq_reglan_of_smt_reglan_from_ih x ihX hx))
      hNonNone
  case re_diff =>
    exact eo_to_smt_typeof_matches_translation_apply_reglan_binop
      UserOp.re_diff SmtTerm.re_diff x y (by rfl)
      (typeof_re_diff_eq (__eo_to_smt y) (__eo_to_smt x))
      (fun hy hx =>
        eo_to_smt_type_typeof_apply_apply_re_diff_of_reglan x y
          (eo_typeof_eq_reglan_of_smt_reglan_from_ih y ihY hy)
          (eo_typeof_eq_reglan_of_smt_reglan_from_ih x ihX hx))
      hNonNone
  case str_in_re =>
    exact eo_to_smt_typeof_matches_translation_apply_seq_char_reglan_binop
      UserOp.str_in_re SmtTerm.str_in_re SmtType.Bool x y (by rfl)
      (typeof_str_in_re_eq (__eo_to_smt y) (__eo_to_smt x))
      (fun hy hx =>
        eo_to_smt_type_typeof_apply_apply_str_in_re_of_seq_char_reglan x y
          (eo_typeof_eq_seq_char_of_smt_seq_char_from_ih y ihY hy)
          (eo_typeof_eq_reglan_of_smt_reglan_from_ih x ihX hx))
      hNonNone
  case seq_nth =>
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) y) x) =
          SmtTerm.seq_nth (__eo_to_smt y) (__eo_to_smt x) := by
      rfl
    have hApplyNN :
        term_has_non_none_type (SmtTerm.seq_nth (__eo_to_smt y) (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    rcases seq_nth_args_of_non_none hApplyNN with ⟨T, hY, hX⟩
    have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
      unfold term_has_non_none_type at hApplyNN
      rw [typeof_seq_nth_eq (__eo_to_smt y) (__eo_to_smt x)] at hApplyNN
      simpa [__smtx_typeof_seq_nth, hY, hX] using hApplyNN
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) y) x)) =
          T := by
      rw [hTranslate]
      have hTy' : __smtx_typeof_guard_wf T T = T :=
        smtx_typeof_guard_wf_of_non_none T T hGuardNN
      rw [typeof_seq_nth_eq (__eo_to_smt y) (__eo_to_smt x)]
      simpa [__smtx_typeof_seq_nth, hY, hX] using hTy'
    rcases eo_typeof_eq_seq_of_smt_seq_from_ih y ihY hY with
      ⟨U, hYU, hU⟩
    have hEo :
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) y) x)) =
          T := by
      simpa [hU] using
        (eo_to_smt_type_typeof_apply_apply_seq_nth_of_seq_int x y U hYU
          (eo_typeof_eq_int_of_smt_int_from_ih x ihX hX))
    exact hSmt.trans
      hEo.symm
  case or =>
    exact eo_to_smt_typeof_matches_translation_apply_bool_binop
        UserOp.or SmtTerm.or x y (by rfl)
        (typeof_or_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun hy hx =>
          eo_to_smt_type_typeof_apply_apply_or_of_bool x y
            (eo_typeof_eq_bool_of_smt_bool_from_ih y ihY hy)
            (eo_typeof_eq_bool_of_smt_bool_from_ih x ihX hx))
        hNonNone
  case and =>
    exact eo_to_smt_typeof_matches_translation_apply_bool_binop
        UserOp.and SmtTerm.and x y (by rfl)
        (typeof_and_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun hy hx =>
          eo_to_smt_type_typeof_apply_apply_and_of_bool x y
            (eo_typeof_eq_bool_of_smt_bool_from_ih y ihY hy)
            (eo_typeof_eq_bool_of_smt_bool_from_ih x ihX hx))
        hNonNone
  case imp =>
    exact eo_to_smt_typeof_matches_translation_apply_bool_binop
        UserOp.imp SmtTerm.imp x y (by rfl)
        (typeof_imp_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun hy hx =>
          eo_to_smt_type_typeof_apply_apply_imp_of_bool x y
            (eo_typeof_eq_bool_of_smt_bool_from_ih y ihY hy)
            (eo_typeof_eq_bool_of_smt_bool_from_ih x ihX hx))
        hNonNone
  case xor =>
    exact eo_to_smt_typeof_matches_translation_apply_bool_binop
        UserOp.xor SmtTerm.xor x y (by rfl)
        (typeof_xor_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun hy hx =>
          eo_to_smt_type_typeof_apply_apply_xor_of_bool x y
            (eo_typeof_eq_bool_of_smt_bool_from_ih y ihY hy)
            (eo_typeof_eq_bool_of_smt_bool_from_ih x ihX hx))
        hNonNone
  case plus =>
    exact eo_to_smt_typeof_matches_translation_apply_arith_binop
      UserOp.plus SmtTerm.plus x y (by rfl)
      (typeof_plus_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun T hy hx hT => by
          rcases hT with rfl | rfl
          · simpa using
              eo_to_smt_type_typeof_apply_apply_plus_of_arith_type x y
                (Term.UOp UserOp.Int)
                (eo_typeof_eq_int_of_smt_int_from_ih y ihY hy)
                (eo_typeof_eq_int_of_smt_int_from_ih x ihX hx)
                (Or.inl rfl)
          · simpa using
              eo_to_smt_type_typeof_apply_apply_plus_of_arith_type x y
                (Term.UOp UserOp.Real)
                (eo_typeof_eq_real_of_smt_real_from_ih y ihY hy)
                (eo_typeof_eq_real_of_smt_real_from_ih x ihX hx)
                (Or.inr rfl))
        hNonNone
  case neg =>
    exact eo_to_smt_typeof_matches_translation_apply_arith_binop
      UserOp.neg SmtTerm.neg x y (by rfl)
      (typeof_neg_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun T hy hx hT => by
          rcases hT with rfl | rfl
          · simpa using
              eo_to_smt_type_typeof_apply_apply_neg_of_arith_type x y
                (Term.UOp UserOp.Int)
                (eo_typeof_eq_int_of_smt_int_from_ih y ihY hy)
                (eo_typeof_eq_int_of_smt_int_from_ih x ihX hx)
                (Or.inl rfl)
          · simpa using
              eo_to_smt_type_typeof_apply_apply_neg_of_arith_type x y
                (Term.UOp UserOp.Real)
                (eo_typeof_eq_real_of_smt_real_from_ih y ihY hy)
                (eo_typeof_eq_real_of_smt_real_from_ih x ihX hx)
                (Or.inr rfl))
        hNonNone
  case mult =>
    exact eo_to_smt_typeof_matches_translation_apply_arith_binop
      UserOp.mult SmtTerm.mult x y (by rfl)
      (typeof_mult_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun T hy hx hT => by
          rcases hT with rfl | rfl
          · simpa using
              eo_to_smt_type_typeof_apply_apply_mult_of_arith_type x y
                (Term.UOp UserOp.Int)
                (eo_typeof_eq_int_of_smt_int_from_ih y ihY hy)
                (eo_typeof_eq_int_of_smt_int_from_ih x ihX hx)
                (Or.inl rfl)
          · simpa using
              eo_to_smt_type_typeof_apply_apply_mult_of_arith_type x y
                (Term.UOp UserOp.Real)
                (eo_typeof_eq_real_of_smt_real_from_ih y ihY hy)
                (eo_typeof_eq_real_of_smt_real_from_ih x ihX hx)
                (Or.inr rfl))
        hNonNone
  case lt =>
    exact eo_to_smt_typeof_matches_translation_apply_arith_bool_binop
      UserOp.lt SmtTerm.lt x y (by rfl)
      (typeof_lt_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun T hy hx hT => by
          rcases hT with rfl | rfl
          · exact eo_to_smt_type_typeof_apply_apply_lt_of_arith_type x y
              (Term.UOp UserOp.Int)
              (eo_typeof_eq_int_of_smt_int_from_ih y ihY hy)
              (eo_typeof_eq_int_of_smt_int_from_ih x ihX hx)
              (Or.inl rfl)
          · exact eo_to_smt_type_typeof_apply_apply_lt_of_arith_type x y
              (Term.UOp UserOp.Real)
              (eo_typeof_eq_real_of_smt_real_from_ih y ihY hy)
              (eo_typeof_eq_real_of_smt_real_from_ih x ihX hx)
              (Or.inr rfl))
        hNonNone
  case leq =>
    exact eo_to_smt_typeof_matches_translation_apply_arith_bool_binop
      UserOp.leq SmtTerm.leq x y (by rfl)
      (typeof_leq_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun T hy hx hT => by
          rcases hT with rfl | rfl
          · exact eo_to_smt_type_typeof_apply_apply_leq_of_arith_type x y
              (Term.UOp UserOp.Int)
              (eo_typeof_eq_int_of_smt_int_from_ih y ihY hy)
              (eo_typeof_eq_int_of_smt_int_from_ih x ihX hx)
              (Or.inl rfl)
          · exact eo_to_smt_type_typeof_apply_apply_leq_of_arith_type x y
              (Term.UOp UserOp.Real)
              (eo_typeof_eq_real_of_smt_real_from_ih y ihY hy)
              (eo_typeof_eq_real_of_smt_real_from_ih x ihX hx)
              (Or.inr rfl))
        hNonNone
  case gt =>
    exact eo_to_smt_typeof_matches_translation_apply_arith_bool_binop
      UserOp.gt SmtTerm.gt x y (by rfl)
      (typeof_gt_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun T hy hx hT => by
          rcases hT with rfl | rfl
          · exact eo_to_smt_type_typeof_apply_apply_gt_of_arith_type x y
              (Term.UOp UserOp.Int)
              (eo_typeof_eq_int_of_smt_int_from_ih y ihY hy)
              (eo_typeof_eq_int_of_smt_int_from_ih x ihX hx)
              (Or.inl rfl)
          · exact eo_to_smt_type_typeof_apply_apply_gt_of_arith_type x y
              (Term.UOp UserOp.Real)
              (eo_typeof_eq_real_of_smt_real_from_ih y ihY hy)
              (eo_typeof_eq_real_of_smt_real_from_ih x ihX hx)
              (Or.inr rfl))
        hNonNone
  case geq =>
    exact eo_to_smt_typeof_matches_translation_apply_arith_bool_binop
      UserOp.geq SmtTerm.geq x y (by rfl)
      (typeof_geq_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun T hy hx hT => by
          rcases hT with rfl | rfl
          · exact eo_to_smt_type_typeof_apply_apply_geq_of_arith_type x y
              (Term.UOp UserOp.Int)
              (eo_typeof_eq_int_of_smt_int_from_ih y ihY hy)
              (eo_typeof_eq_int_of_smt_int_from_ih x ihX hx)
              (Or.inl rfl)
          · exact eo_to_smt_type_typeof_apply_apply_geq_of_arith_type x y
              (Term.UOp UserOp.Real)
              (eo_typeof_eq_real_of_smt_real_from_ih y ihY hy)
              (eo_typeof_eq_real_of_smt_real_from_ih x ihX hx)
              (Or.inr rfl))
        hNonNone
  case div =>
    exact eo_to_smt_typeof_matches_translation_apply_int_binop
        UserOp.div SmtTerm.div SmtType.Int x y (by rfl)
        (typeof_div_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun hy hx =>
          eo_to_smt_type_typeof_apply_apply_div_of_int x y
            (eo_typeof_eq_int_of_smt_int_from_ih y ihY hy)
            (eo_typeof_eq_int_of_smt_int_from_ih x ihX hx))
        hNonNone
  case mod =>
    exact eo_to_smt_typeof_matches_translation_apply_int_binop
        UserOp.mod SmtTerm.mod SmtType.Int x y (by rfl)
        (typeof_mod_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun hy hx =>
          eo_to_smt_type_typeof_apply_apply_mod_of_int x y
            (eo_typeof_eq_int_of_smt_int_from_ih y ihY hy)
            (eo_typeof_eq_int_of_smt_int_from_ih x ihX hx))
        hNonNone
  case divisible =>
    exact eo_to_smt_typeof_matches_translation_apply_int_binop
        UserOp.divisible SmtTerm.divisible SmtType.Bool x y (by rfl)
        (typeof_divisible_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun hy hx =>
          eo_to_smt_type_typeof_apply_apply_divisible_of_int x y
            (eo_typeof_eq_int_of_smt_int_from_ih y ihY hy)
            (eo_typeof_eq_int_of_smt_int_from_ih x ihX hx))
        hNonNone
  case div_total =>
    exact eo_to_smt_typeof_matches_translation_apply_int_binop
        UserOp.div_total SmtTerm.div_total SmtType.Int x y (by rfl)
        (typeof_div_total_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun hy hx =>
          eo_to_smt_type_typeof_apply_apply_div_total_of_int x y
            (eo_typeof_eq_int_of_smt_int_from_ih y ihY hy)
            (eo_typeof_eq_int_of_smt_int_from_ih x ihX hx))
        hNonNone
  case mod_total =>
    exact eo_to_smt_typeof_matches_translation_apply_int_binop
        UserOp.mod_total SmtTerm.mod_total SmtType.Int x y (by rfl)
        (typeof_mod_total_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun hy hx =>
          eo_to_smt_type_typeof_apply_apply_mod_total_of_int x y
            (eo_typeof_eq_int_of_smt_int_from_ih y ihY hy)
            (eo_typeof_eq_int_of_smt_int_from_ih x ihX hx))
        hNonNone
  case qdiv =>
    exact eo_to_smt_typeof_matches_translation_apply_arith_ret_binop
      UserOp.qdiv SmtTerm.qdiv SmtType.Real x y (by rfl)
      (typeof_qdiv_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun T hy hx hT => by
          rcases hT with rfl | rfl
          · exact eo_to_smt_type_typeof_apply_apply_qdiv_of_arith_type x y
              (Term.UOp UserOp.Int)
              (eo_typeof_eq_int_of_smt_int_from_ih y ihY hy)
              (eo_typeof_eq_int_of_smt_int_from_ih x ihX hx)
              (Or.inl rfl)
          · exact eo_to_smt_type_typeof_apply_apply_qdiv_of_arith_type x y
              (Term.UOp UserOp.Real)
              (eo_typeof_eq_real_of_smt_real_from_ih y ihY hy)
              (eo_typeof_eq_real_of_smt_real_from_ih x ihX hx)
              (Or.inr rfl))
        hNonNone
  case qdiv_total =>
    exact eo_to_smt_typeof_matches_translation_apply_arith_ret_binop
      UserOp.qdiv_total SmtTerm.qdiv_total SmtType.Real x y (by rfl)
      (typeof_qdiv_total_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun T hy hx hT => by
          rcases hT with rfl | rfl
          · exact eo_to_smt_type_typeof_apply_apply_qdiv_total_of_arith_type x y
              (Term.UOp UserOp.Int)
              (eo_typeof_eq_int_of_smt_int_from_ih y ihY hy)
              (eo_typeof_eq_int_of_smt_int_from_ih x ihX hx)
              (Or.inl rfl)
          · exact eo_to_smt_type_typeof_apply_apply_qdiv_total_of_arith_type x y
              (Term.UOp UserOp.Real)
              (eo_typeof_eq_real_of_smt_real_from_ih y ihY hy)
              (eo_typeof_eq_real_of_smt_real_from_ih x ihX hx)
              (Or.inr rfl))
        hNonNone
  case select =>
    exact eo_to_smt_typeof_matches_translation_apply_select x y ihY ihX hNonNone
  case concat =>
    exact eo_to_smt_typeof_matches_translation_apply_concat x y
      (by rfl)
      (fun w1 w2 hy hx => by
        have hSum : (0 : Int) ≤ (w1 : Int) + (w2 : Int) := by omega
        simpa [__eo_to_smt_type, __eo_mk_apply, __eo_add, native_ite, native_zleq,
          SmtEval.native_zleq, SmtEval.native_zplus, Smtm.native_nat_to_int,
          hSum] using
          eo_to_smt_type_typeof_apply_apply_concat_of_bitvec_types x y
            (Term.Numeral (native_nat_to_int w1))
            (Term.Numeral (native_nat_to_int w2))
            (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w1 hy)
            (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w2 hx))
      hNonNone
  case bvand =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvand) SmtTerm.bvand x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvand_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvor =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvor) SmtTerm.bvor x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvor_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvnand =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvnand) SmtTerm.bvnand x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvnand_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvnor =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvnor) SmtTerm.bvnor x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvnor_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvxor =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvxor) SmtTerm.bvxor x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvxor_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvxnor =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvxnor) SmtTerm.bvxnor x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvxnor_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvcomp =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
      (Term.UOp UserOp.bvcomp) SmtTerm.bvcomp (SmtType.BitVec 1) x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvcomp_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvadd =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvadd) SmtTerm.bvadd x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvadd_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvmul =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvmul) SmtTerm.bvmul x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvmul_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvudiv =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvudiv) SmtTerm.bvudiv x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvudiv_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvurem =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvurem) SmtTerm.bvurem x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvurem_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvsub =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvsub) SmtTerm.bvsub x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsub_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvsdiv =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvsdiv) SmtTerm.bvsdiv x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsdiv_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvsrem =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvsrem) SmtTerm.bvsrem x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsrem_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvsmod =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvsmod) SmtTerm.bvsmod x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsmod_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvult =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
      (Term.UOp UserOp.bvult) SmtTerm.bvult SmtType.Bool x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvult_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvule =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
      (Term.UOp UserOp.bvule) SmtTerm.bvule SmtType.Bool x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvule_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvugt =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
      (Term.UOp UserOp.bvugt) SmtTerm.bvugt SmtType.Bool x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvugt_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvuge =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
      (Term.UOp UserOp.bvuge) SmtTerm.bvuge SmtType.Bool x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvuge_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvslt =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
      (Term.UOp UserOp.bvslt) SmtTerm.bvslt SmtType.Bool x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvslt_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvsle =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
      (Term.UOp UserOp.bvsle) SmtTerm.bvsle SmtType.Bool x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsle_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvsgt =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
      (Term.UOp UserOp.bvsgt) SmtTerm.bvsgt SmtType.Bool x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsgt_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvsge =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
      (Term.UOp UserOp.bvsge) SmtTerm.bvsge SmtType.Bool x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsge_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvshl =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvshl) SmtTerm.bvshl x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvshl_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvlshr =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvlshr) SmtTerm.bvlshr x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvlshr_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvashr =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvashr) SmtTerm.bvashr x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvashr_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvuaddo =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
      (Term.UOp UserOp.bvuaddo) SmtTerm.bvuaddo SmtType.Bool x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvuaddo_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvsaddo =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
      (Term.UOp UserOp.bvsaddo) SmtTerm.bvsaddo SmtType.Bool x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsaddo_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvumulo =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
      (Term.UOp UserOp.bvumulo) SmtTerm.bvumulo SmtType.Bool x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvumulo_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvsmulo =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
      (Term.UOp UserOp.bvsmulo) SmtTerm.bvsmulo SmtType.Bool x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsmulo_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvusubo =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
      (Term.UOp UserOp.bvusubo) SmtTerm.bvusubo SmtType.Bool x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvusubo_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvssubo =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
      (Term.UOp UserOp.bvssubo) SmtTerm.bvssubo SmtType.Bool x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvssubo_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvsdivo =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
      (Term.UOp UserOp.bvsdivo) SmtTerm.bvsdivo SmtType.Bool x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsdivo_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvultbv =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_cmp_to_bv1
      (Term.UOp UserOp.bvultbv) SmtTerm.bvult x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => by
        simpa using eo_to_smt_type_typeof_apply_apply_bvultbv_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvsltbv =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_cmp_to_bv1
      (Term.UOp UserOp.bvsltbv) SmtTerm.bvslt x y
      (by rfl)
      (by rw [__smtx_typeof.eq_def] <;> simp only)
      (fun w hy hx => by
        simpa using eo_to_smt_type_typeof_apply_apply_bvsltbv_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case str_at =>
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_at) y) x) =
          SmtTerm.str_at (__eo_to_smt y) (__eo_to_smt x) := by
      rfl
    have hApplyNN :
        term_has_non_none_type (SmtTerm.str_at (__eo_to_smt y) (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    rcases str_at_args_of_non_none hApplyNN with ⟨T, hY, hX⟩
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_at) y) x)) =
          SmtType.Seq T := by
      rw [hTranslate, typeof_str_at_eq (__eo_to_smt y) (__eo_to_smt x), hY, hX]
      simp [__smtx_typeof_str_at]
    have hYTrans :
        __eo_to_smt_type (__eo_typeof y) = SmtType.Seq T := by
      have hTyped := ihY (by rw [hY]; simp)
      rw [hY] at hTyped
      exact hTyped.symm
    rcases eo_typeof_eq_seq_of_smt_seq_from_ih y ihY hY with ⟨U, hYSeq, hU⟩
    have hTGuard :
        __smtx_typeof_guard T (SmtType.Seq T) = SmtType.Seq T := by
      simpa [hYSeq, hU, __eo_to_smt_type] using hYTrans
    have hTNN : T ≠ SmtType.None := by
      intro hNone
      rw [hNone] at hTGuard
      simp [__smtx_typeof_guard, native_ite, native_Teq] at hTGuard
    have hXInt : __eo_typeof x = Term.UOp UserOp.Int :=
      eo_typeof_eq_int_of_smt_int_from_ih x ihX hX
    have hEo :
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.str_at) y) x)) =
          SmtType.Seq T := by
      simpa [__eo_to_smt_type, hU, smtx_typeof_guard_of_non_none T (SmtType.Seq T) hTNN] using
        eo_to_smt_type_typeof_apply_apply_str_at_of_seq_int x y U hYSeq hXInt
    exact hSmt.trans hEo.symm
  case _at_from_bools =>
    exact eo_to_smt_typeof_matches_translation_apply_at_from_bools x y ihY ihX hNonNone
  case _at_strings_num_occur =>
    exact eo_to_smt_typeof_matches_translation_apply_at_strings_num_occur
      x y ihY ihX hNonNone
  case _at_array_deq_diff =>
    exact eo_to_smt_typeof_matches_translation_array_deq_diff y x
      ihY (fun hNN => (ihYAll hNN).2) ihX (fun hNN => (ihXAll hNN).2)
      hNonNone
  case _at_strings_deq_diff =>
    exact (eo_to_smt_typeof_matches_translation_apply_at_strings_deq_diff
      x y ihY ihX hNonNone).1
  case _at_strings_stoi_result =>
    exact eo_to_smt_typeof_matches_translation_apply_at_strings_stoi_result
      x y ihY ihX hNonNone
  case _at_strings_itos_result =>
    exact eo_to_smt_typeof_matches_translation_apply_at_strings_itos_result
      x y ihY ihX hNonNone
  case _at_strings_num_occur_re =>
    exact eo_to_smt_typeof_matches_translation_apply_at_strings_num_occur_re
      x y ihY ihX hNonNone
  case _at_strings_replace_all_result =>
    exact False.elim (hNonNone (by
      change
        __smtx_typeof
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt y)) (__eo_to_smt x)) =
          SmtType.None
      exact typeof_apply_apply_none_head_eq (__eo_to_smt y) (__eo_to_smt x)))
  case _at_sets_deq_diff =>
    exact eo_to_smt_typeof_matches_translation_sets_deq_diff y x
      ihY (fun hNN => (ihYAll hNN).2) ihX (fun hNN => (ihXAll hNN).2)
      hNonNone
  case tuple =>
    exact eo_to_smt_typeof_matches_translation_apply_tuple
      x y ihYAll ihXAll hNonNone
  case set_union =>
    exact eo_to_smt_typeof_matches_translation_apply_set_binop
      UserOp.set_union SmtTerm.set_union x y ihY ihX (by rfl)
      (typeof_set_union_eq (__eo_to_smt y) (__eo_to_smt x))
      (by rfl)
      hNonNone
  case set_inter =>
    exact eo_to_smt_typeof_matches_translation_apply_set_binop
      UserOp.set_inter SmtTerm.set_inter x y ihY ihX (by rfl)
      (typeof_set_inter_eq (__eo_to_smt y) (__eo_to_smt x))
      (by rfl)
      hNonNone
  case set_minus =>
    exact eo_to_smt_typeof_matches_translation_apply_set_binop
      UserOp.set_minus SmtTerm.set_minus x y ihY ihX (by rfl)
      (typeof_set_minus_eq (__eo_to_smt y) (__eo_to_smt x))
      (by rfl)
      hNonNone
  case set_member =>
    exact eo_to_smt_typeof_matches_translation_apply_set_member_from_ih
      x y ihY ihX hNonNone
  case set_subset =>
    exact eo_to_smt_typeof_matches_translation_apply_set_pred_binop
      UserOp.set_subset SmtTerm.set_subset x y ihY ihX (by rfl)
      (typeof_set_subset_eq (__eo_to_smt y) (__eo_to_smt x))
      (by rfl)
      hNonNone
  case set_choose =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_generic_from_ih
      (Term.UOp UserOp.set_choose) y x ihFAll
      ihXAll
      (generic_apply_type_of_non_special_head _ _
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h))
      (by rfl) (by rfl) hNonNone
  case set_insert =>
    exact eo_to_smt_typeof_matches_translation_apply_set_insert
      x y ihX ihBelowAll hNonNone
  case «forall» =>
    exact eo_to_smt_typeof_matches_translation_apply_forall_from_ih
      x y ihX hNonNone
  case «exists» =>
    exact eo_to_smt_typeof_matches_translation_apply_exists_from_ih
      x y ihX hNonNone
  case _at__at_Pair =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_none_head
      UserOp._at__at_Pair y x (by rfl) hNonNone
  case _at__at_pair =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_none_head
      UserOp._at__at_pair y x (by rfl) hNonNone
  case _at__at_TypedList_cons =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_none_head
      UserOp._at__at_TypedList_cons y x (by rfl) hNonNone
  case Array =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_none_head
      UserOp.Array y x (by rfl) hNonNone
  case Tuple =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_none_head
      UserOp.Tuple y x (by rfl) hNonNone
  case _at__at_mon =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_none_head
      UserOp._at__at_mon y x (by rfl) hNonNone
  case _at__at_poly =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_none_head
      UserOp._at__at_poly y x (by rfl) hNonNone
  case _at__at_aci_sorted =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_none_head
      UserOp._at__at_aci_sorted y x (by rfl) hNonNone
  all_goals
    exact eo_to_smt_typeof_matches_translation_apply_apply_generic_from_ih
      _ y x ihFAll ihXAll
      (generic_apply_type_of_non_special_head _ _
        (by intro s d i j h; exact (eo_to_smt_apply_ne_dt_sel _ y s d i j h).elim)
        (by intro s d i h; exact (eo_to_smt_apply_ne_dt_tester _ y s d i h).elim))
      (by rfl) (by rfl) hNonNone

/-- Handles `(UOp op) y` heads in the nested-application apply proof. -/
private theorem eo_to_smt_typeof_matches_translation_apply_uop_application_head
    (op : UserOp) (y x : Term)
    (ihF :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp op) y)) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp op) y)) =
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp op) y)) ∧
        eo_type_valid (__eo_typeof (Term.Apply (Term.UOp op) y)))
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y) ∧
        eo_type_valid (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) ∧
        eo_type_valid (__eo_typeof x))
    (ihBelowAll :
      ∀ term,
        sizeOf term < sizeOf (Term.Apply (Term.Apply (Term.UOp op) y) x) ->
        __smtx_typeof (__eo_to_smt term) ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt term) = __eo_to_smt_type (__eo_typeof term) ∧
          eo_type_valid (__eo_typeof term)) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) y) x)) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp op) y) x)) := by
  intro hNonNone
  exact eo_to_smt_typeof_matches_translation_apply_uop_application_head_obligation
    op y x ihF ihY ihX ihBelowAll hNonNone

/-- Top-level valid EO types are injective under translation, including `RegLan`. -/
private theorem eo_to_smt_type_eq_of_top_valid_apply
    {T U : Term}
    (hValid : eo_type_valid T)
    (hEq : __eo_to_smt_type T = __eo_to_smt_type U) :
    T = U := by
  exact eo_to_smt_type_eq_of_valid hValid hEq

/-- Ternary `ite`, using local IHs to align branch EO types. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_ite_from_valid_ih
    (x y z : Term)
    (ihZ :
      __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z))
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y) ∧
          eo_type_valid (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) z) y) x)) ≠
        SmtType.None) :
      __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) z) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) z) y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) z) y) x) =
        SmtTerm.ite (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hApplyNN :
      term_has_non_none_type (SmtTerm.ite (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases ite_args_of_non_none hApplyNN with ⟨T, hZ, hY, hX, hTNN⟩
  have hSmt :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) z) y) x)) =
        T := by
    rw [hTranslate, typeof_ite_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)]
    rw [hZ, hY, hX]
    simp [__smtx_typeof_ite, native_ite, native_Teq]
  have hZNN : __smtx_typeof (__eo_to_smt z) ≠ SmtType.None := by
    rw [hZ]
    simp
  have hYNN : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
    rw [hY]
    exact hTNN
  have hXNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hX]
    exact hTNN
  have hzEo : __eo_typeof z = Term.Bool := by
    apply eo_to_smt_type_eq_bool
    rw [← ihZ hZNN, hZ]
  have hYTrans : __eo_to_smt_type (__eo_typeof y) = T := by
    rw [← (ihY hYNN).1, hY]
  have hXTrans : __eo_to_smt_type (__eo_typeof x) = T := by
    rw [← ihX hXNN, hX]
  have hYValidTop : eo_type_valid (__eo_typeof y) :=
    (ihY hYNN).2
  have hEqEo : __eo_typeof x = __eo_typeof y := by
    have hYX : __eo_typeof y = __eo_typeof x := by
      apply eo_to_smt_type_eq_of_top_valid_apply hYValidTop
      exact hYTrans.trans hXTrans.symm
    exact hYX.symm
  have hYTypeNN : __eo_to_smt_type (__eo_typeof y) ≠ SmtType.None := by
    rw [hYTrans]
    exact hTNN
  have hEo :
      __eo_to_smt_type
          (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) z) y) x)) =
        T :=
    (eo_to_smt_type_typeof_apply_apply_apply_ite_of_bool_same_type
      x y z (__eo_typeof y) hzEo rfl hEqEo hYTypeNN).trans hYTrans
  exact hSmt.trans hEo.symm

private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_ite_from_ih
    (x y z : Term)
    (ihZ :
      __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z))
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y) ∧
        eo_type_valid (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) z) y) x)) ≠
        SmtType.None) :
      __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) z) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) z) y) x)) := by
  exact
    eo_to_smt_typeof_matches_translation_apply_apply_apply_ite_from_valid_ih
      x y z ihZ ihY ihX hNonNone

/-- Ternary `bvite`, using local IHs to align branch EO types. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_bvite_from_valid_ih
    (x y z : Term)
    (ihZ :
      __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z))
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y) ∧
          eo_type_valid (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) z) y) x)) ≠
        SmtType.None) :
      __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) z) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) z) y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) z) y) x) =
        SmtTerm.ite
          (SmtTerm.eq (__eo_to_smt z) (SmtTerm.Binary 1 1))
          (__eo_to_smt y)
          (__eo_to_smt x) := by
    rfl
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.ite
          (SmtTerm.eq (__eo_to_smt z) (SmtTerm.Binary 1 1))
          (__eo_to_smt y)
          (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases ite_args_of_non_none hApplyNN with ⟨T, hCond, hY, hX, hTNN⟩
  have hCondNN :
      __smtx_typeof
          (SmtTerm.eq (__eo_to_smt z) (SmtTerm.Binary 1 1)) ≠
        SmtType.None := by
    rw [hCond]
    simp
  have hEqNN :
      __smtx_typeof_eq (__smtx_typeof (__eo_to_smt z)) (SmtType.BitVec 1) ≠
        SmtType.None := by
    rw [typeof_eq_eq, typeof_binary_one_eq] at hCondNN
    exact hCondNN
  have hZ : __smtx_typeof (__eo_to_smt z) = SmtType.BitVec 1 :=
    (smtx_typeof_eq_non_none hEqNN).1
  have hSmt :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) z) y) x)) =
        T := by
    rw [hTranslate]
    rw [typeof_ite_eq]
    rw [hCond, hY, hX]
    simp [__smtx_typeof_ite, native_ite, native_Teq]
  have hZNN : __smtx_typeof (__eo_to_smt z) ≠ SmtType.None := by
    rw [hZ]
    simp
  have hYNN : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
    rw [hY]
    exact hTNN
  have hXNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hX]
    exact hTNN
  have hzEo :
      __eo_typeof z = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
    have hzEo' := eo_typeof_eq_bitvec_of_smt_bitvec_from_ih z ihZ 1 hZ
    simpa [native_nat_to_int, Smtm.native_nat_to_int] using hzEo'
  have hYTrans : __eo_to_smt_type (__eo_typeof y) = T := by
    rw [← (ihY hYNN).1, hY]
  have hXTrans : __eo_to_smt_type (__eo_typeof x) = T := by
    rw [← ihX hXNN, hX]
  have hYValidTop : eo_type_valid (__eo_typeof y) :=
    (ihY hYNN).2
  have hEqEo : __eo_typeof x = __eo_typeof y := by
    have hYX : __eo_typeof y = __eo_typeof x := by
      apply eo_to_smt_type_eq_of_top_valid_apply hYValidTop
      exact hYTrans.trans hXTrans.symm
    exact hYX.symm
  have hYTypeNN : __eo_to_smt_type (__eo_typeof y) ≠ SmtType.None := by
    rw [hYTrans]
    exact hTNN
  have hEo :
      __eo_to_smt_type
          (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) z) y) x)) =
        T :=
    (eo_to_smt_type_typeof_apply_apply_apply_bvite_of_bitvec1_same_type
      x y z (__eo_typeof y) hzEo rfl hEqEo hYTypeNN).trans hYTrans
  exact hSmt.trans hEo.symm

private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_bvite_from_ih
    (x y z : Term)
    (ihZ :
      __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z))
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y) ∧
        eo_type_valid (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) z) y) x)) ≠
        SmtType.None) :
      __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) z) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) z) y) x)) := by
  exact
    eo_to_smt_typeof_matches_translation_apply_apply_apply_bvite_from_valid_ih
      x y z ihZ ihY ihX hNonNone

/-- Simplifies EO-to-SMT translation for ternary bitvector `extract`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_extract
    (x y z : Term)
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp2 UserOp2.extract z y) x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp2 UserOp2.extract z y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract z y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.UOp2 UserOp2.extract z y) x) =
        SmtTerm.extract (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.extract (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases extract_args_of_non_none hApplyNN with ⟨i, j, w, hZ, hY, hX, hj0, hWidth, hiw⟩
  have hWidthEq :
      native_zplus (native_zplus i 1) (native_zneg j) =
        native_zplus (native_zplus i (native_zneg j)) 1 := by
    simp [SmtEval.native_zplus, SmtEval.native_zneg, Int.add_assoc, Int.add_comm,
      Int.add_left_comm]
  have hWidthPos :
      native_zlt 0 (native_zplus (native_zplus i (native_zneg j)) 1) = true := by
    rw [← hWidthEq]
    exact hWidth
  have hWidthOld :
      native_zleq 0 (native_zplus (native_zplus i (native_zneg j)) 1) = true :=
    native_zleq_of_zlt_true _ _ hWidthPos
  have hSmt :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp2 UserOp2.extract z y) x)) =
        SmtType.BitVec
          (native_int_to_nat (native_zplus (native_zplus i (native_zneg j)) 1)) := by
    rw [hTranslate, typeof_extract_eq, hZ, hY, hX]
    simp [__smtx_typeof_extract, native_ite, hj0, hiw, hWidthPos, hWidthEq]
  have hEo :
      __eo_to_smt_type
          (__eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract z y) x)) =
        SmtType.BitVec
          (native_int_to_nat (native_zplus (native_zplus i (native_zneg j)) 1)) := by
    have hZTerm : z = Term.Numeral i :=
      eo_to_smt_eq_numeral z i hZ
    have hYTerm : y = Term.Numeral j :=
      eo_to_smt_eq_numeral y j hY
    have hXEo :
        __eo_typeof x =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w)) :=
      eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hX
    have hEoRaw :=
      eo_to_smt_type_typeof_apply_apply_apply_extract_of_int_int_bitvec_type
        x z y (Term.Numeral (native_nat_to_int w))
        (by rw [hZTerm]; rfl)
        (by rw [hYTerm]; rfl)
        hXEo
    have hLoGtNegOne :
        native_zlt (-1 : native_Int) j = true :=
      native_zlt_neg_one_of_zleq_zero (n := j) hj0
    have hWidthNonneg :
        native_zleq 0 (native_zplus (native_zplus i (native_zneg j)) 1) = true :=
      hWidthOld
    rw [hEoRaw]
    rw [hZTerm, hYTerm]
    simp [__eo_mk_apply, __eo_requires, __eo_gt,
      __eo_add, __eo_neg, native_ite, native_teq, native_not,
      hLoGtNegOne, hiw, hWidthPos, hWidthNonneg]
  exact hSmt.trans hEo.symm

/-- Proof for `_at_witness_string_length`. -/
theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_at_witness_string_length
    (x y z : Term)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt
            (Term.UOp3 UserOp3._at_witness_string_length z y x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt
          (Term.UOp3 UserOp3._at_witness_string_length z y x)) =
      __eo_to_smt_type
        (__eo_typeof
          (Term.UOp3 UserOp3._at_witness_string_length z y x)) := by
  let T := __eo_to_smt_type z
  let body :=
    SmtTerm.eq
      (SmtTerm.str_len (SmtTerm.Var (native_string_lit "@x") T))
      (__eo_to_smt y)
  have hTranslate :
      __eo_to_smt
          (Term.UOp3 UserOp3._at_witness_string_length z y x) =
        native_ite (__eo_to_smt_nat_is_valid y)
          (native_ite (__eo_to_smt_nat_is_valid x)
            (SmtTerm.choice (native_string_lit "@x") T body)
            SmtTerm.None)
          SmtTerm.None := by
    rfl
  have hYValid : __eo_to_smt_nat_is_valid y = true := by
    cases hTest : __eo_to_smt_nat_is_valid y
    · exfalso
      apply hNonNone
      rw [hTranslate]
      simp [hTest, native_ite]
    · rfl
  have hXValid : __eo_to_smt_nat_is_valid x = true := by
    cases hTest : __eo_to_smt_nat_is_valid x
    · exfalso
      apply hNonNone
      rw [hTranslate]
      simp [hYValid, hTest, native_ite]
    · rfl
  have hXInt : __eo_typeof x = Term.UOp UserOp.Int :=
    eo_typeof_eq_int_of_nat_is_valid x hXValid
  have hYInt : __eo_typeof y = Term.UOp UserOp.Int :=
    eo_typeof_eq_int_of_nat_is_valid y hYValid
  have hChoiceNN : term_has_non_none_type (SmtTerm.choice (native_string_lit "@x") T body) := by
    unfold term_has_non_none_type
    have hTermNN := hNonNone
    rw [hTranslate] at hTermNN
    simpa [hYValid, hXValid, native_ite] using hTermNN
  have hChoiceTy :
      __smtx_typeof (SmtTerm.choice (native_string_lit "@x") T body) = T :=
    choice_term_typeof_of_non_none hChoiceNN
  have hSmt :
    __smtx_typeof
          (__eo_to_smt
            (Term.UOp3 UserOp3._at_witness_string_length z y x)) =
        T := by
    rw [hTranslate]
    simpa [hYValid, hXValid, native_ite] using hChoiceTy
  have hChoiceGuard :
      __smtx_typeof (SmtTerm.choice (native_string_lit "@x") T body) =
        __smtx_typeof_guard_wf T T :=
    choice_term_guard_type_of_non_none hChoiceNN
  have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    intro hNone
    unfold term_has_non_none_type at hChoiceNN
    exact hChoiceNN (by rw [hChoiceGuard, hNone])
  have hTWF : __smtx_type_wf T = true :=
    Smtm.smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
  have hZType : __eo_typeof z = Term.Type :=
    eo_typeof_type_of_smt_type_wf z (by simpa [T] using hTWF)
  have hEo :
      __eo_to_smt_type
          (__eo_typeof
            (Term.UOp3 UserOp3._at_witness_string_length z y x)) =
        T := by
    simpa [T] using
      eo_to_smt_type_typeof_apply_apply_apply_at_witness_string_length_of_type_int_int
        x y z hZType hYInt hXInt
  exact hSmt.trans hEo.symm

/-- `str_substr`, using the local IHs to recover EO argument types. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_str_substr_from_ih
    (x y z : Term)
    (ihZ :
      __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z))
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) z) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) z) y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) z) y) x) =
        SmtTerm.str_substr (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.str_substr (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases str_substr_args_of_non_none hApplyNN with ⟨T, hZ, hY, hX⟩
  have hSmt :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) z) y) x)) =
        SmtType.Seq T := by
    rw [hTranslate, typeof_str_substr_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)]
    simp [__smtx_typeof_str_substr, hZ, hY, hX]
  have hZTrans :
      __eo_to_smt_type (__eo_typeof z) = SmtType.Seq T := by
    have hTyped := ihZ (by rw [hZ]; simp)
    rw [hZ] at hTyped
    exact hTyped.symm
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih z ihZ hZ with ⟨U, hZSeq, hU⟩
  have hTGuard :
      __smtx_typeof_guard T (SmtType.Seq T) = SmtType.Seq T := by
    simpa [hZSeq, hU, __eo_to_smt_type] using hZTrans
  have hTNN : T ≠ SmtType.None := by
    intro hNone
    rw [hNone] at hTGuard
    simp [__smtx_typeof_guard, native_ite, native_Teq] at hTGuard
  have hYInt : __eo_typeof y = Term.UOp UserOp.Int :=
    eo_typeof_eq_int_of_smt_int_from_ih y ihY hY
  have hXInt : __eo_typeof x = Term.UOp UserOp.Int :=
    eo_typeof_eq_int_of_smt_int_from_ih x ihX hX
  have hEo :
      __eo_to_smt_type
          (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) z) y) x)) =
        SmtType.Seq T := by
    simpa [__eo_to_smt_type, hU, smtx_typeof_guard_of_non_none T (SmtType.Seq T) hTNN] using
      eo_to_smt_type_typeof_apply_apply_apply_str_substr_of_seq_int_int
        x y z U hZSeq hYInt hXInt
  exact hSmt.trans hEo.symm

/-- `str_indexof`, using local IHs to recover EO argument types. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_str_indexof_from_ih
    (x y z : Term)
    (ihZ :
      __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z))
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) z) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) z) y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) z) y) x) =
        SmtTerm.str_indexof (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.str_indexof (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases str_indexof_args_of_non_none hApplyNN with ⟨T, hZ, hY, hX⟩
  have hSmt :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) z) y) x)) =
        SmtType.Int := by
    rw [hTranslate, typeof_str_indexof_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)]
    simp [__smtx_typeof_str_indexof, native_ite, native_Teq, hZ, hY, hX]
  have hTWF :
      smtx_type_field_wf_rec T native_reflist_nil :=
    smtx_seq_component_field_wf_rec_of_non_none_type_apply (__eo_to_smt z) T hZ
  have hTNN : T ≠ SmtType.None := by
    intro hNone
    subst T
    simp [smtx_type_field_wf_rec, __smtx_type_wf_rec] at hTWF
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih z ihZ hZ with ⟨U, hZU, hU⟩
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih y ihY hY with ⟨V, hYV, hV⟩
  have hVU : V = U :=
    eo_to_smt_type_injective_of_field_wf_rec hV hU hTWF
  have hYU : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) U := by
    rw [hYV, hVU]
  have hXInt : __eo_typeof x = Term.UOp UserOp.Int :=
    eo_typeof_eq_int_of_smt_int_from_ih x ihX hX
  have hEo :
      __eo_to_smt_type
          (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) z) y) x)) =
        SmtType.Int :=
    eo_to_smt_type_typeof_apply_apply_apply_str_indexof_of_seq_seq_int
      x y z U hZU hYU hXInt (by rw [hU]; exact hTNN)
  exact hSmt.trans hEo.symm

private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_at_strings_occur_index
    (x y z : Term)
    (ihZ :
      __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z))
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_occur_index) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_occur_index) z) y) x)) =
      __eo_to_smt_type
        (__eo_typeof
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_occur_index) z) y) x)) := by
  have hTranslate :
      __eo_to_smt
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_occur_index) z) y) x) =
        SmtTerm._at_strings_occur_index
          (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hOccurNN :
      term_has_non_none_type
        (SmtTerm._at_strings_occur_index
          (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases smt_strings_occur_index_args_of_non_none
      (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) hOccurNN with
    ⟨T, hZ, hY, hX, hOccurTy⟩
  have hSmt :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_occur_index) z) y) x)) =
        SmtType.Int := by
    rw [hTranslate]
    exact hOccurTy
  have hTWF :
      smtx_type_field_wf_rec T native_reflist_nil :=
    smtx_seq_component_field_wf_rec_of_non_none_type_apply (__eo_to_smt z) T hZ
  have hTNN : T ≠ SmtType.None := by
    intro hNone
    subst T
    simp [smtx_type_field_wf_rec, __smtx_type_wf_rec] at hTWF
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih z ihZ hZ with ⟨U, hZU, hU⟩
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih y ihY hY with ⟨V, hYV, hV⟩
  have hVU : V = U :=
    eo_to_smt_type_injective_of_field_wf_rec hV hU hTWF
  have hYU : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) U := by
    rw [hYV, hVU]
  have hXInt : __eo_typeof x = Term.UOp UserOp.Int :=
    eo_typeof_eq_int_of_smt_int_from_ih x ihX hX
  have hUNS : U ≠ Term.Stuck :=
    eo_term_ne_stuck_of_smt_type_non_none U (by rw [hU]; exact hTNN)
  have hEo :
      __eo_to_smt_type
          (__eo_typeof
            (Term.Apply
              (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_occur_index) z) y) x)) =
        SmtType.Int := by
    change
      __eo_to_smt_type
          (__eo_typeof_str_indexof (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
        SmtType.Int
    rw [hZU, hYU, hXInt]
    simpa [__eo_typeof_str_indexof] using
      congrArg __eo_to_smt_type
        (eo_requires_eo_eq_self_of_non_stuck U (Term.UOp UserOp.Int) hUNS)
  exact hSmt.trans hEo.symm

private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_at_strings_occur_index_re
    (x y z : Term)
    (ihZ :
      __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z))
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_occur_index_re) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_occur_index_re) z) y) x)) =
      __eo_to_smt_type
        (__eo_typeof
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_occur_index_re) z) y) x)) := by
  have hTranslate :
      __eo_to_smt
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_occur_index_re) z) y) x) =
        SmtTerm._at_strings_occur_index_re
          (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hOccurNN :
      term_has_non_none_type
        (SmtTerm._at_strings_occur_index_re
          (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  have hArgs :=
    smt_strings_occur_index_re_args_of_non_none
      (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) hOccurNN
  have hSmt :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_occur_index_re) z) y) x)) =
        SmtType.Int := by
    rw [hTranslate]
    exact hArgs.2.2.2
  have hZEo : __eo_typeof z = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) :=
    eo_typeof_eq_seq_char_of_smt_seq_char_from_ih z ihZ hArgs.1
  have hYEo : __eo_typeof y = Term.UOp UserOp.RegLan :=
    eo_typeof_eq_reglan_of_smt_reglan_from_ih y ihY hArgs.2.1
  have hXEo : __eo_typeof x = Term.UOp UserOp.Int :=
    eo_typeof_eq_int_of_smt_int_from_ih x ihX hArgs.2.2.1
  have hEo :
      __eo_to_smt_type
          (__eo_typeof
            (Term.Apply
              (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_occur_index_re) z) y) x)) =
        SmtType.Int := by
    change
      __eo_to_smt_type
          (__eo_typeof_str_indexof_re (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
        SmtType.Int
    rw [hZEo, hYEo, hXEo]
    rfl
  exact hSmt.trans hEo.symm

private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_apply_at_strings_replace_all_result
    (x y z w : Term)
    (ihW :
      __smtx_typeof (__eo_to_smt w) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt w) = __eo_to_smt_type (__eo_typeof w))
    (ihZ :
      __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z))
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp._at_strings_replace_all_result) w) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.UOp UserOp._at_strings_replace_all_result) w) z) y) x)) =
      __eo_to_smt_type
        (__eo_typeof
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.UOp UserOp._at_strings_replace_all_result) w) z) y) x)) := by
  let start :=
    SmtTerm._at_strings_occur_index
      (__eo_to_smt w) (__eo_to_smt z) (__eo_to_smt x)
  let suffix :=
    SmtTerm.str_substr (__eo_to_smt w) start (SmtTerm.str_len (__eo_to_smt w))
  have hTranslate :
      __eo_to_smt
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.UOp UserOp._at_strings_replace_all_result) w) z) y) x) =
        SmtTerm.str_replace_all suffix (__eo_to_smt z) (__eo_to_smt y) := by
    rfl
  have hReplaceNN :
      term_has_non_none_type
        (SmtTerm.str_replace_all suffix (__eo_to_smt z) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace_all)
      (typeof_str_replace_all_eq suffix (__eo_to_smt z) (__eo_to_smt y))
      hReplaceNN with
    ⟨T, hSuffix, hZ, hY⟩
  have hSuffixNN : term_has_non_none_type suffix := by
    unfold term_has_non_none_type
    rw [hSuffix]
    simp
  rcases str_substr_args_of_non_none (by simpa [suffix] using hSuffixNN) with
    ⟨U, hW, hStart, hLength⟩
  have hSuffixU : __smtx_typeof suffix = SmtType.Seq U := by
    simp [suffix, typeof_str_substr_eq, __smtx_typeof_str_substr,
      hW, hStart, hLength]
  have hUT : U = T := by
    have hEq : SmtType.Seq U = SmtType.Seq T := hSuffixU.symm.trans hSuffix
    cases hEq
    rfl
  subst U
  have hStartNN : term_has_non_none_type start := by
    unfold term_has_non_none_type
    rw [hStart]
    simp
  rcases smt_strings_occur_index_args_of_non_none
      (__eo_to_smt w) (__eo_to_smt z) (__eo_to_smt x)
      (by simpa [start] using hStartNN) with
    ⟨V, _hWFromStart, _hZFromStart, hX, _hStartTy⟩
  have hSmt :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp._at_strings_replace_all_result) w) z) y) x)) =
        SmtType.Seq T := by
    rw [hTranslate, typeof_str_replace_all_eq, hSuffix, hZ, hY]
    simp [__smtx_typeof_seq_op_3, native_ite, native_Teq]
  have hTWF :
      smtx_type_field_wf_rec T native_reflist_nil :=
    smtx_seq_component_field_wf_rec_of_non_none_type_apply (__eo_to_smt w) T hW
  have hTNN : T ≠ SmtType.None := by
    intro hNone
    subst T
    simp [smtx_type_field_wf_rec, __smtx_type_wf_rec] at hTWF
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih w ihW hW with ⟨A, hWA, hA⟩
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih z ihZ hZ with ⟨B, hZB, hB⟩
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih y ihY hY with ⟨C, hYC, hC⟩
  have hBA : B = A :=
    eo_to_smt_type_injective_of_field_wf_rec hB hA hTWF
  have hCA : C = A :=
    eo_to_smt_type_injective_of_field_wf_rec hC hA hTWF
  have hZA : __eo_typeof z = Term.Apply (Term.UOp UserOp.Seq) A := by
    rw [hZB, hBA]
  have hYA : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) A := by
    rw [hYC, hCA]
  have hXInt : __eo_typeof x = Term.UOp UserOp.Int :=
    eo_typeof_eq_int_of_smt_int_from_ih x ihX hX
  have hANS : A ≠ Term.Stuck :=
    eo_term_ne_stuck_of_smt_type_non_none A (by rw [hA]; exact hTNN)
  have hEoRaw :
      __eo_typeof
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.UOp UserOp._at_strings_replace_all_result) w) z) y) x) =
        Term.Apply (Term.UOp UserOp.Seq) A := by
    change
      __eo_typeof__at_strings_replace_all_result
          (__eo_typeof w) (__eo_typeof z) (__eo_typeof y) (__eo_typeof x) =
        Term.Apply (Term.UOp UserOp.Seq) A
    rw [hWA, hZA, hYA, hXInt]
    simpa [__eo_typeof__at_strings_replace_all_result] using
      eo_requires_eo_and_eq_self_of_non_stuck
        A A (Term.Apply (Term.UOp UserOp.Seq) A) hANS hANS
  have hSeqA :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) A) = SmtType.Seq T := by
    simp [__eo_to_smt_type, hA,
      smtx_typeof_guard_of_non_none T (SmtType.Seq T) hTNN]
  rw [hEoRaw, hSeqA]
  exact hSmt

private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_apply_at_strings_replace_re_all_result
    (x y z w : Term)
    (ihW :
      __smtx_typeof (__eo_to_smt w) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt w) = __eo_to_smt_type (__eo_typeof w))
    (ihZ :
      __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z))
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp._at_strings_replace_re_all_result) w) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.UOp UserOp._at_strings_replace_re_all_result) w) z) y) x)) =
      __eo_to_smt_type
        (__eo_typeof
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.UOp UserOp._at_strings_replace_re_all_result) w) z) y) x)) := by
  let start :=
    SmtTerm._at_strings_occur_index_re
      (__eo_to_smt w) (__eo_to_smt z) (__eo_to_smt x)
  let suffix :=
    SmtTerm.str_substr (__eo_to_smt w) start (SmtTerm.str_len (__eo_to_smt w))
  have hTranslate :
      __eo_to_smt
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.UOp UserOp._at_strings_replace_re_all_result) w) z) y) x) =
        SmtTerm.str_replace_re_all suffix (__eo_to_smt z) (__eo_to_smt y) := by
    rfl
  have hReplaceNN :
      term_has_non_none_type
        (SmtTerm.str_replace_re_all suffix (__eo_to_smt z) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  have hReplaceArgs :=
    str_replace_re_args_of_non_none (op := SmtTerm.str_replace_re_all)
      (typeof_str_replace_re_all_eq suffix (__eo_to_smt z) (__eo_to_smt y))
      hReplaceNN
  have hSuffixNN : term_has_non_none_type suffix := by
    unfold term_has_non_none_type
    rw [hReplaceArgs.1]
    simp
  rcases str_substr_args_of_non_none (by simpa [suffix] using hSuffixNN) with
    ⟨T, hW, hStart, _hLength⟩
  have hWChar : __smtx_typeof (__eo_to_smt w) = SmtType.Seq SmtType.Char := by
    have hSuffixT : __smtx_typeof suffix = SmtType.Seq T := by
      simp [suffix, typeof_str_substr_eq, __smtx_typeof_str_substr,
        hW, hStart, _hLength]
    have hTChar : T = SmtType.Char := by
      have hEq : SmtType.Seq T = SmtType.Seq SmtType.Char :=
        hSuffixT.symm.trans hReplaceArgs.1
      cases hEq
      rfl
    simpa [hTChar] using hW
  have hStartNN : term_has_non_none_type start := by
    unfold term_has_non_none_type
    rw [hStart]
    simp
  have hOccurArgs :=
    smt_strings_occur_index_re_args_of_non_none
      (__eo_to_smt w) (__eo_to_smt z) (__eo_to_smt x)
      (by simpa [start] using hStartNN)
  have hSmt :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp._at_strings_replace_re_all_result) w) z) y) x)) =
        SmtType.Seq SmtType.Char := by
    rw [hTranslate, typeof_str_replace_re_all_eq]
    simp [native_ite, native_Teq, hReplaceArgs.1, hReplaceArgs.2.1,
      hReplaceArgs.2.2]
  have hWEo : __eo_typeof w = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) :=
    eo_typeof_eq_seq_char_of_smt_seq_char_from_ih w ihW hWChar
  have hZEo : __eo_typeof z = Term.UOp UserOp.RegLan :=
    eo_typeof_eq_reglan_of_smt_reglan_from_ih z ihZ hReplaceArgs.2.1
  have hYEo : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) :=
    eo_typeof_eq_seq_char_of_smt_seq_char_from_ih y ihY hReplaceArgs.2.2
  have hXEo : __eo_typeof x = Term.UOp UserOp.Int :=
    eo_typeof_eq_int_of_smt_int_from_ih x ihX hOccurArgs.2.2.1
  have hEo :
      __eo_to_smt_type
          (__eo_typeof
            (Term.Apply
              (Term.Apply
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp._at_strings_replace_re_all_result) w) z) y) x)) =
        SmtType.Seq SmtType.Char := by
    change
      __eo_to_smt_type
          (__eo_typeof__at_strings_replace_re_all_result
            (__eo_typeof w) (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
        SmtType.Seq SmtType.Char
    rw [hWEo, hZEo, hYEo, hXEo]
    rfl
  exact hSmt.trans hEo.symm

/-- `str_update`, using local IHs to recover EO argument types. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_str_update_from_ih
    (x y z : Term)
    (ihZ :
      __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z))
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) z) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) z) y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) z) y) x) =
        SmtTerm.str_update (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.str_update (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases str_update_args_of_non_none hApplyNN with ⟨T, hZ, hY, hX⟩
  have hSmt :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) z) y) x)) =
        SmtType.Seq T := by
    rw [hTranslate, typeof_str_update_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)]
    simp [__smtx_typeof_str_update, native_ite, native_Teq, hZ, hY, hX]
  have hTWF :
      smtx_type_field_wf_rec T native_reflist_nil :=
    smtx_seq_component_field_wf_rec_of_non_none_type_apply (__eo_to_smt z) T hZ
  have hTNN : T ≠ SmtType.None := by
    intro hNone
    subst T
    simp [smtx_type_field_wf_rec, __smtx_type_wf_rec] at hTWF
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih z ihZ hZ with ⟨U, hZU, hU⟩
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih x ihX hX with ⟨V, hXV, hV⟩
  have hVU : V = U :=
    eo_to_smt_type_injective_of_field_wf_rec hV hU hTWF
  have hXU : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) U := by
    rw [hXV, hVU]
  have hYInt : __eo_typeof y = Term.UOp UserOp.Int :=
    eo_typeof_eq_int_of_smt_int_from_ih y ihY hY
  have hEo :
      __eo_to_smt_type
          (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) z) y) x)) =
        SmtType.Seq T := by
    have hSeqU :
        __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U) = SmtType.Seq T := by
      simp [__eo_to_smt_type, hU,
        smtx_typeof_guard_of_non_none T (SmtType.Seq T) hTNN]
    exact
      (eo_to_smt_type_typeof_apply_apply_apply_str_update_of_seq_int_seq
        x y z U hZU hYInt hXU (by rw [hU]; exact hTNN)).trans hSeqU
  exact hSmt.trans hEo.symm

/-- Simplifies EO-to-SMT translation for sequence ternary operators returning a sequence. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_seq_triop
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm)
    (x y z : Term)
    (ihZ :
      __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z))
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) z) y) x) =
        smtOp (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_seq_op_3
          (__smtx_typeof (__eo_to_smt z))
          (__smtx_typeof (__eo_to_smt y))
          (__smtx_typeof (__eo_to_smt x)))
    (hEo :
      ∀ {T : Term},
        __eo_typeof z = Term.Apply (Term.UOp UserOp.Seq) T ->
        __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) T ->
        __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) T ->
        __eo_to_smt_type T ≠ SmtType.None ->
        __eo_to_smt_type
            (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) z) y) x)) =
          __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) z) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) z) y) x)) := by
  have hApplyNN :
      term_has_non_none_type (smtOp (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases seq_triop_args_of_non_none (op := smtOp) hTy hApplyNN with
    ⟨T, hZ, hY, hX⟩
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) z) y) x)) =
        SmtType.Seq T := by
    rw [hTranslate, hTy, hZ, hY, hX]
    simp [__smtx_typeof_seq_op_3, native_ite, native_Teq]
  have hTWF :
      smtx_type_field_wf_rec T native_reflist_nil :=
    smtx_seq_component_field_wf_rec_of_non_none_type_apply (__eo_to_smt z) T hZ
  have hTNN : T ≠ SmtType.None := by
    intro hNone
    subst T
    simp [smtx_type_field_wf_rec, __smtx_type_wf_rec] at hTWF
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih z ihZ hZ with ⟨U, hZU, hU⟩
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih y ihY hY with ⟨V, hYV, hV⟩
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih x ihX hX with ⟨W, hXW, hW⟩
  have hVU : V = U :=
    eo_to_smt_type_injective_of_field_wf_rec hV hU hTWF
  have hWU : W = U :=
    eo_to_smt_type_injective_of_field_wf_rec hW hU hTWF
  have hYU : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) U := by
    rw [hYV, hVU]
  have hXU : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) U := by
    rw [hXW, hWU]
  have hEoTy :
      __eo_to_smt_type
          (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) z) y) x)) =
        SmtType.Seq T := by
    have hSeqU :
        __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U) = SmtType.Seq T := by
      simp [__eo_to_smt_type, hU,
        smtx_typeof_guard_of_non_none T (SmtType.Seq T) hTNN]
    exact (hEo (T := U) hZU hYU hXU (by rw [hU]; exact hTNN)).trans hSeqU
  exact hSmt.trans hEoTy.symm

/-- Simplifies EO-to-SMT translation for regex-replacement ternary string operators. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_str_replace_re_like
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm)
    (x y z : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) z) y) x) =
        smtOp (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) =
        native_ite (native_Teq (__smtx_typeof (__eo_to_smt z)) (SmtType.Seq SmtType.Char))
          (native_ite (native_Teq (__smtx_typeof (__eo_to_smt y)) SmtType.RegLan)
            (native_ite (native_Teq (__smtx_typeof (__eo_to_smt x)) (SmtType.Seq SmtType.Char))
              (SmtType.Seq SmtType.Char) SmtType.None)
            SmtType.None)
          SmtType.None)
    (hEo :
      __smtx_typeof (__eo_to_smt z) = SmtType.Seq SmtType.Char ->
      __smtx_typeof (__eo_to_smt y) = SmtType.RegLan ->
      __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char ->
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) z) y) x)) =
        SmtType.Seq SmtType.Char)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) z) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) z) y) x)) := by
  have hApplyNN :
      term_has_non_none_type (smtOp (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  have hArgs := str_replace_re_args_of_non_none (op := smtOp) hTy hApplyNN
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) z) y) x)) =
        SmtType.Seq SmtType.Char := by
    rw [hTranslate, hTy]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2.1, hArgs.2.2]
  exact hSmt.trans (hEo hArgs.1 hArgs.2.1 hArgs.2.2).symm

/-- `str_indexof_re`, using local IHs to recover EO argument types. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_str_indexof_re_from_ih
    (x y z : Term)
    (ihZ :
      __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z))
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) z) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) z) y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) z) y) x) =
        SmtTerm.str_indexof_re (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.str_indexof_re (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  have hArgs := str_indexof_re_args_of_non_none hApplyNN
  have hSmt :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) z) y) x)) =
        SmtType.Int := by
    rw [hTranslate, typeof_str_indexof_re_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2.1, hArgs.2.2]
  have hEo :
      __eo_to_smt_type
          (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) z) y) x)) =
        SmtType.Int :=
    eo_to_smt_type_typeof_apply_apply_apply_str_indexof_re_of_seq_char_reglan
      x y z
      (eo_typeof_eq_seq_char_of_smt_seq_char_from_ih z ihZ hArgs.1)
      (eo_typeof_eq_reglan_of_smt_reglan_from_ih y ihY hArgs.2.1)
      (eo_typeof_eq_int_of_smt_int_from_ih x ihX hArgs.2.2)
  exact hSmt.trans hEo.symm

/-- Ternary `store`, using local IHs to recover the EO array shape. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_store_from_ih
    (x y z : Term)
    (ihZ :
      __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z))
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) z) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) z) y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) z) y) x) =
        SmtTerm.store (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hApplyNN :
      term_has_non_none_type (SmtTerm.store (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases store_args_of_non_none hApplyNN with ⟨A, B, hZ, hY, hX⟩
  have hSmt :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) z) y) x)) =
        SmtType.Map A B := by
    rw [hTranslate, typeof_store_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)]
    simp [__smtx_typeof_store, native_ite, native_Teq, hZ, hY, hX]
  have hComps :=
    smtx_map_components_field_wf_rec_of_non_none_type_apply (__eo_to_smt z) A B hZ
  have hANN : A ≠ SmtType.None :=
    smtx_type_field_wf_rec_ne_none hComps.1
  have hBNN : B ≠ SmtType.None :=
    smtx_type_field_wf_rec_ne_none hComps.2
  rcases eo_typeof_eq_map_of_smt_map_from_ih z ihZ hZ with
    ⟨U, T, hZArray, hU, hT⟩
  have hYTrans : __eo_to_smt_type (__eo_typeof y) = A := by
    have hYNN : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
      rw [hY]
      exact hANN
    rw [← ihY hYNN]
    exact hY
  have hXTrans : __eo_to_smt_type (__eo_typeof x) = B := by
    have hXNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hX]
      exact hBNN
    rw [← ihX hXNN]
    exact hX
  have hYU : __eo_typeof y = U :=
    eo_to_smt_type_injective_of_field_wf_rec hYTrans hU hComps.1
  have hXT : __eo_typeof x = T :=
    eo_to_smt_type_injective_of_field_wf_rec hXTrans hT hComps.2
  have hUNN : __eo_to_smt_type U ≠ SmtType.None := by
    rw [hU]
    exact hANN
  have hTNN : __eo_to_smt_type T ≠ SmtType.None := by
    rw [hT]
    exact hBNN
  have hEo :
      __eo_to_smt_type
          (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) z) y) x)) =
        SmtType.Map A B := by
    simpa [hU, hT] using
      eo_to_smt_type_typeof_apply_apply_apply_store_of_array
        x y z U T hZArray hYU hXT hUNN hTNN
  exact hSmt.trans hEo.symm

/-- Simplifies EO-to-SMT translation for ternary `re_loop`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_re_loop
    (x y z : Term)
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp2 UserOp2.re_loop z y) x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp2 UserOp2.re_loop z y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.UOp2 UserOp2.re_loop z y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.UOp2 UserOp2.re_loop z y) x) =
        SmtTerm.re_loop (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.re_loop (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  cases hz : __eo_to_smt z with
  | Numeral n1 =>
      cases hy : __eo_to_smt y with
      | Numeral n2 =>
          have hLoopNN :
              term_has_non_none_type
                (SmtTerm.re_loop
                  (SmtTerm.Numeral n1)
                  (SmtTerm.Numeral n2)
                  (__eo_to_smt x)) := by
            simpa [hz, hy] using hApplyNN
          rcases re_loop_arg_of_non_none hLoopNN with ⟨hn1, hn2, hX⟩
          have hSmt :
              __smtx_typeof
                  (__eo_to_smt
                    (Term.Apply (Term.UOp2 UserOp2.re_loop z y) x)) =
                SmtType.RegLan := by
            rw [hTranslate, hz, hy]
            rw [typeof_re_loop_eq (SmtTerm.Numeral n1) (SmtTerm.Numeral n2) (__eo_to_smt x)]
            simp [__smtx_typeof_re_loop, hX, hn1, hn2, native_ite]
          have hZInt : __smtx_typeof (__eo_to_smt z) = SmtType.Int := by
            rw [hz]
            unfold __smtx_typeof
            rfl
          have hYInt : __smtx_typeof (__eo_to_smt y) = SmtType.Int := by
            rw [hy]
            unfold __smtx_typeof
            rfl
          have hZTerm : z = Term.Numeral n1 :=
            eo_to_smt_eq_numeral z n1 hz
          have hYTerm : y = Term.Numeral n2 :=
            eo_to_smt_eq_numeral y n2 hy
          have hZEo : __eo_typeof z = Term.UOp UserOp.Int := by
            rw [hZTerm]
            rfl
          have hYEo : __eo_typeof y = Term.UOp UserOp.Int := by
            rw [hYTerm]
            rfl
          have hXEo : __eo_typeof x = Term.UOp UserOp.RegLan :=
            eo_typeof_eq_reglan_of_smt_reglan_from_ih x ihX hX
          have hEo :
              __eo_to_smt_type
                  (__eo_typeof
                    (Term.Apply (Term.UOp2 UserOp2.re_loop z y) x)) =
                SmtType.RegLan := by
            change
              __eo_to_smt_type
                  (__eo_typeof_re_loop (__eo_typeof z) z (__eo_typeof y) y (__eo_typeof x)) =
                SmtType.RegLan
            have hn1Gt : native_zlt (-1 : native_Int) n1 = true :=
              native_zlt_neg_one_of_zleq_zero hn1
            have hn2Gt : native_zlt (-1 : native_Int) n2 = true :=
              native_zlt_neg_one_of_zleq_zero hn2
            rw [hZTerm, hYTerm, hXEo]
            change
              __eo_to_smt_type
                  (__eo_typeof_re_loop (Term.UOp UserOp.Int) (Term.Numeral n1)
                    (Term.UOp UserOp.Int) (Term.Numeral n2)
                    (Term.UOp UserOp.RegLan)) =
                SmtType.RegLan
            simp [__eo_typeof_re_loop, __eo_gt, __eo_requires, native_teq,
              native_not, native_ite, hn1Gt, hn2Gt]
          exact hSmt.trans hEo.symm
      | _ =>
          exfalso
          unfold term_has_non_none_type at hApplyNN
          rw [hz, hy, typeof_re_loop_eq] at hApplyNN
          simp [__smtx_typeof_re_loop] at hApplyNN
  | _ =>
      exfalso
      unfold term_has_non_none_type at hApplyNN
      rw [hz, typeof_re_loop_eq] at hApplyNN
      simp [__smtx_typeof_re_loop] at hApplyNN

/-- Handles ternary applications whose binary head translates to a non-special SMT term. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
    (op : UserOp) (z y x : Term)
    (ihF :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y)) ≠
        SmtType.None ->
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y)) =
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp op) z) y)) ∧
        eo_type_valid (__eo_typeof (Term.Apply (Term.Apply (Term.UOp op) z) y)))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) ∧
        eo_type_valid (__eo_typeof x))
    (head : SmtTerm)
    (hHeadTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y) = head)
    (hOuterTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y)) (__eo_to_smt x))
    (hSel : ∀ s d i j, head ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, head ≠ SmtTerm.DtTester s d i)
    (hEoApply :
      __eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x) =
        __eo_typeof_apply (__eo_typeof (Term.Apply (Term.Apply (Term.UOp op) z) y))
          (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) := by
  have hGeneric :
      generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y))
        (__eo_to_smt x) := by
    rw [hHeadTranslate]
    exact generic_apply_type_of_non_special_head head (__eo_to_smt x) hSel hTester
  exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_from_ih
    (Term.UOp op) z y x ihF ihX hGeneric hOuterTranslate hEoApply hNonNone

/-- Handles ternary applications whose binary head is itself a generic application. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_application_head
    (g z y x : Term)
    (ihF :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply g z) y)) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply g z) y)) =
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply g z) y)) ∧
        eo_type_valid (__eo_typeof (Term.Apply (Term.Apply g z) y)))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) ∧
        eo_type_valid (__eo_typeof x))
    (hOuterTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply g z) y) x) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply g z) y)) (__eo_to_smt x))
    (hEoApply :
      __eo_typeof (Term.Apply (Term.Apply (Term.Apply g z) y) x) =
        __eo_typeof_apply (__eo_typeof (Term.Apply (Term.Apply g z) y)) (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply g z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply g z) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply g z) y) x)) := by
  have hGeneric :
      generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply g z) y)) (__eo_to_smt x) := by
    exact generic_apply_type_of_non_special_head
      (__eo_to_smt (Term.Apply (Term.Apply g z) y)) (__eo_to_smt x)
      (by intro s d i j; exact eo_to_smt_apply_ne_dt_sel (Term.Apply g z) y s d i j)
      (by intro s d i; exact eo_to_smt_apply_ne_dt_tester (Term.Apply g z) y s d i)
  exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_from_ih
    g z y x ihF ihX hGeneric hOuterTranslate hEoApply hNonNone

/-- Closes attempts to apply a one-bit bitvector comparison result as a function. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_bv_cmp_to_bv1_applied
    (op : UserOp) (smtCmp : SmtTerm -> SmtTerm -> SmtTerm) (x y z : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x) =
        SmtTerm.Apply
          (SmtTerm.ite (smtCmp (__eo_to_smt z) (__eo_to_smt y))
            (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0))
          (__eo_to_smt x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) := by
  let head :=
    SmtTerm.ite (smtCmp (__eo_to_smt z) (__eo_to_smt y))
      (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)
  have hApplyNN :
      __smtx_typeof_apply (__smtx_typeof head) (__smtx_typeof (__eo_to_smt x)) ≠
        SmtType.None := by
    have hHeadGeneric : generic_apply_type head (__eo_to_smt x) := by
      exact generic_apply_type_of_non_special_head _ _
        (by intro s d i j h; simp [head] at h)
        (by intro s d i h; simp [head] at h)
    have hApplyNN' :
        __smtx_typeof (SmtTerm.Apply head (__eo_to_smt x)) ≠ SmtType.None := by
      simpa [head, hTranslate] using hNonNone
    rw [hHeadGeneric] at hApplyNN'
    exact hApplyNN'
  rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
  have hHeadNN : __smtx_typeof head ≠ SmtType.None := by
    rcases hHead with hHead | hHead <;> rw [hHead] <;> simp
  have hIteNN : term_has_non_none_type head := by
    unfold term_has_non_none_type
    exact hHeadNN
  rcases ite_args_of_non_none hIteNN with ⟨T, hCond, hThen, hElse, hT⟩
  have hThenNN : __smtx_typeof (SmtTerm.Binary 1 1) ≠ SmtType.None := by
    rw [hThen]
    exact hT
  have hBitVec1 : T = SmtType.BitVec 1 := by
    exact hThen.symm.trans (smtx_typeof_binary_of_non_none 1 1 hThenNN)
  have hHeadTy : __smtx_typeof head = T := by
    unfold head
    rw [typeof_ite_eq]
    rw [hCond, hThen, hElse]
    simp [__smtx_typeof_ite, native_ite, native_Teq]
  rcases hHead with hHead | hHead
  · cases (hBitVec1.symm.trans (hHeadTy.symm.trans hHead))
  · cases (hBitVec1.symm.trans (hHeadTy.symm.trans hHead))

/-- Simplifies EO-to-SMT translation for `_at_re_unfold_pos_component`. -/
theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_re_unfold_pos_component
    (x y z : Term)
    (ihZ :
      __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z))
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt (Term._at_re_unfold_pos_component z y x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt (Term._at_re_unfold_pos_component z y x)) =
      __eo_to_smt_type
        (__eo_typeof (Term._at_re_unfold_pos_component z y x)) ∧
      eo_type_valid (__eo_typeof (Term._at_re_unfold_pos_component z y x)) := by
  have hTranslate :
      __eo_to_smt (Term._at_re_unfold_pos_component z y x) =
        native_ite (__eo_to_smt_nat_is_valid x)
          (__eo_to_smt_re_unfold_pos_component
            (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt_nat x))
          SmtTerm.None := by
    rfl
  cases hValid : __eo_to_smt_nat_is_valid x
  · exfalso
    apply hNonNone
    rw [hTranslate, hValid]
    simp [native_ite]
  · have hCompNN :
        term_has_non_none_type
          (__eo_to_smt_re_unfold_pos_component
            (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt_nat x)) := by
      unfold term_has_non_none_type
      have hNN := hNonNone
      rw [hTranslate, hValid] at hNN
      simpa [native_ite] using hNN
    have hArgs :=
      re_unfold_pos_component_args_of_non_none
        (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt_nat x) hCompNN
    have hSmt :
        __smtx_typeof
            (__eo_to_smt (Term._at_re_unfold_pos_component z y x)) =
          SmtType.Seq SmtType.Char := by
      rw [hTranslate, hValid]
      simp [native_ite]
      exact smtx_typeof_re_unfold_pos_component_of_non_none
        (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt_nat x)
        (by
          unfold term_has_non_none_type at hCompNN
          exact hCompNN)
    have hXInt : __eo_typeof x = Term.UOp UserOp.Int := by
      cases x <;> simp [__eo_to_smt_nat_is_valid] at hValid
      case Numeral n => rfl
    have hZEo : __eo_typeof z =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) :=
      eo_typeof_eq_seq_char_of_smt_seq_char_from_ih z ihZ hArgs.1
    have hYEo : __eo_typeof y = Term.UOp UserOp.RegLan :=
      eo_typeof_eq_reglan_of_smt_reglan_from_ih y ihY hArgs.2
    have hEo :
        __eo_to_smt_type
            (__eo_typeof (Term._at_re_unfold_pos_component z y x)) =
          SmtType.Seq SmtType.Char :=
      eo_to_smt_type_typeof_apply_apply_apply_re_unfold_pos_component_of_seq_char_reglan_int
        x y z hZEo hYEo hXInt
    refine ⟨hSmt.trans hEo.symm, ?_⟩
    have hType :
        __eo_typeof (Term._at_re_unfold_pos_component z y x) =
          Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
      change
        __eo_typeof__at_re_unfold_pos_component
          (__eo_typeof z) (__eo_typeof y) (__eo_typeof x) =
          Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
      rw [hZEo, hYEo, hXInt]
      rfl
    rw [hType]
    simp [eo_type_valid, noNoneTy, __smtx_typeof_guard,
      native_ite, native_Teq]

/-- Closes attempts to apply a binary head already known to have SMT type `Bool`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_bool_head_applied
    (op : UserOp) (head : SmtTerm) (x y z : Term)
    (hHeadTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y) = head)
    (hOuterTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y))
          (__eo_to_smt x))
    (hGeneric :
      generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y))
        (__eo_to_smt x))
    (hHeadBool :
      term_has_non_none_type head ->
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y)) =
          SmtType.Bool)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) := by
  have hApplyNN :
      __smtx_typeof_apply
          (__smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y)))
          (__smtx_typeof (__eo_to_smt x)) ≠
        SmtType.None := by
    have hApplyNN' :
        __smtx_typeof
            (SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y))
              (__eo_to_smt x)) ≠
          SmtType.None := by
      rw [← hOuterTranslate]
      exact hNonNone
    rw [hGeneric] at hApplyNN'
    exact hApplyNN'
  rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
  have hHeadNN : term_has_non_none_type head := by
    unfold term_has_non_none_type
    rw [← hHeadTranslate]
    rcases hHead with hHead | hHead <;> rw [hHead] <;> simp
  have hHeadTy := hHeadBool hHeadNN
  rcases hHead with hHead | hHead
  · cases (hHeadTy.symm.trans hHead)
  · cases (hHeadTy.symm.trans hHead)

/- Closes attempts to apply a non-special binary head known to have SMT type `Bool`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_bool_non_special_head_applied
    (op : UserOp) (head : SmtTerm) (x y z : Term)
    (hHeadTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y) = head)
    (hOuterTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y))
          (__eo_to_smt x))
    (hHeadType :
      term_has_non_none_type head ->
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y)) =
          SmtType.Bool)
    (hSel : ∀ s d i j, head ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, head ≠ SmtTerm.DtTester s d i)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) := by
  have hGeneric :
      generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y))
        (__eo_to_smt x) := by
    rw [hHeadTranslate]
    exact generic_apply_type_of_non_special_head head (__eo_to_smt x) hSel hTester
  exact eo_to_smt_typeof_matches_translation_apply_apply_apply_bool_head_applied
    op head x y z hHeadTranslate hOuterTranslate hGeneric hHeadType hNonNone

/-- Closes attempts to apply a binary head known to have a non-function SMT type. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_non_function_head_applied
    (op : UserOp) (head : SmtTerm) (x y z : Term)
    (hHeadTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y) = head)
    (hOuterTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y))
          (__eo_to_smt x))
    (hGeneric :
      generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y))
        (__eo_to_smt x))
    (hHeadType :
      term_has_non_none_type head ->
        ∃ T,
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y)) = T ∧
            (∀ A B, T ≠ SmtType.FunType A B) ∧
            (∀ A B, T ≠ SmtType.FunType A B) ∧
            (∀ A B, T ≠ SmtType.DtcAppType A B))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) := by
  have hApplyNN :
      __smtx_typeof_apply
          (__smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y)))
          (__smtx_typeof (__eo_to_smt x)) ≠
        SmtType.None := by
    have hApplyNN' :
        __smtx_typeof
            (SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y))
              (__eo_to_smt x)) ≠
          SmtType.None := by
      rw [← hOuterTranslate]
      exact hNonNone
    rw [hGeneric] at hApplyNN'
    exact hApplyNN'
  rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
  have hHeadNN : term_has_non_none_type head := by
    unfold term_has_non_none_type
    rw [← hHeadTranslate]
    rcases hHead with hHead | hHead <;> rw [hHead] <;> simp
  rcases hHeadType hHeadNN with ⟨T, hHeadTy, hNotFun, hNotIFun, hNotDtcApp⟩
  have _ := hNotIFun
  rcases hHead with hHead | hHead
  · exact False.elim (hNotFun A B (hHeadTy.symm.trans hHead))
  · exact False.elim (hNotDtcApp A B (hHeadTy.symm.trans hHead))

/-- Closes attempts to apply a non-special binary head with any non-function SMT type. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_non_function_non_special_head_applied
    (op : UserOp) (head : SmtTerm) (x y z : Term)
    (hHeadTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y) = head)
    (hOuterTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y))
          (__eo_to_smt x))
    (hHeadType :
      term_has_non_none_type head ->
        ∃ T,
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y)) = T ∧
            (∀ A B, T ≠ SmtType.FunType A B) ∧
            (∀ A B, T ≠ SmtType.FunType A B) ∧
            (∀ A B, T ≠ SmtType.DtcAppType A B))
    (hSel : ∀ s d i j, head ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, head ≠ SmtTerm.DtTester s d i)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) := by
  have hGeneric :
      generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y))
        (__eo_to_smt x) := by
    rw [hHeadTranslate]
    exact generic_apply_type_of_non_special_head head (__eo_to_smt x) hSel hTester
  exact eo_to_smt_typeof_matches_translation_apply_apply_apply_non_function_head_applied
    op head x y z hHeadTranslate hOuterTranslate hGeneric hHeadType hNonNone


private theorem smtx_apply_arg_non_none_of_non_none
    (f x : SmtTerm)
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i)
    (hNN : __smtx_typeof (SmtTerm.Apply f x) ≠ SmtType.None) :
    __smtx_typeof x ≠ SmtType.None := by
  have hApply :
      __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None := by
    cases f
    case DtSel s d i j =>
      exact False.elim (hSel s d i j rfl)
    case DtTester s d i =>
      exact False.elim (hTester s d i rfl)
    all_goals
      simpa [__smtx_typeof] using hNN
  rcases typeof_apply_non_none_cases hApply with ⟨A, _B, _hHead, hArg, hA, _hB⟩
  rw [hArg]
  exact hA

private theorem smtx_apply_head_non_none_of_non_none
    (f x : SmtTerm)
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i)
    (hNN : __smtx_typeof (SmtTerm.Apply f x) ≠ SmtType.None) :
    __smtx_typeof f ≠ SmtType.None := by
  have hApply :
      __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None := by
    cases f
    case DtSel s d i j =>
      exact False.elim (hSel s d i j rfl)
    case DtTester s d i =>
      exact False.elim (hTester s d i rfl)
    all_goals
      simpa [__smtx_typeof] using hNN
  rcases typeof_apply_non_none_cases hApply with ⟨A, B, hHead, _hArg, _hA, _hB⟩
  rcases hHead with hHead | hHead
  · rw [hHead]
    simp
  · rw [hHead]
    simp

private theorem eo_to_smt_updater_rec_ne_dt_sel
    (s : native_String) (d : SmtDatatypeDecl) (i j n : native_Nat) (t u acc : SmtTerm)
    (hAccSel : ∀ s d i j, acc ≠ SmtTerm.DtSel s d i j)
    (s0 : native_String) (d0 : SmtDatatypeDecl) (i0 j0 : native_Nat) :
    __eo_to_smt_updater_rec (SmtTerm.DtSel s d i j) n t u acc ≠
      SmtTerm.DtSel s0 d0 i0 j0 := by
  intro h
  cases n with
  | zero =>
      simpa [__eo_to_smt_updater_rec] using hAccSel s0 d0 i0 j0 h
  | succ k =>
      cases h

private theorem eo_to_smt_updater_rec_ne_dt_tester
    (s : native_String) (d : SmtDatatypeDecl) (i j n : native_Nat) (t u acc : SmtTerm)
    (hAccTester : ∀ s d i, acc ≠ SmtTerm.DtTester s d i)
    (s0 : native_String) (d0 : SmtDatatypeDecl) (i0 : native_Nat) :
    __eo_to_smt_updater_rec (SmtTerm.DtSel s d i j) n t u acc ≠
      SmtTerm.DtTester s0 d0 i0 := by
  intro h
  cases n with
  | zero =>
      simpa [__eo_to_smt_updater_rec] using hAccTester s0 d0 i0 h
  | succ k =>
      cases h

theorem eo_to_smt_updater_rec_update_arg_non_none_of_non_none
    (s : native_String) (d : SmtDatatypeDecl) (i j n : native_Nat) (t u acc : SmtTerm)
    (hAccSel : ∀ s d i j, acc ≠ SmtTerm.DtSel s d i j)
    (hAccTester : ∀ s d i, acc ≠ SmtTerm.DtTester s d i)
    (hIdx : native_zlt (native_nat_to_int j) (native_nat_to_int n) = true)
    (hNN :
      __smtx_typeof
          (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j) n t u acc) ≠
        SmtType.None) :
    __smtx_typeof u ≠ SmtType.None := by
  induction n generalizing acc with
  | zero =>
      have hIdx' := hIdx
      unfold native_zlt at hIdx'
      have hjInt := of_decide_eq_true hIdx'
      unfold native_nat_to_int at hjInt
      have hj : j < Nat.zero := Int.ofNat_lt.mp hjInt
      exact (Nat.not_lt_zero j hj).elim
  | succ k ih =>
      by_cases hEq : native_nateq j k = true
      · have hRecSel :
            ∀ s0 d0 i0 j0,
              __eo_to_smt_updater_rec (SmtTerm.DtSel s d i j) k t u acc ≠
                SmtTerm.DtSel s0 d0 i0 j0 :=
          eo_to_smt_updater_rec_ne_dt_sel s d i j k t u acc hAccSel
        have hRecTester :
            ∀ s0 d0 i0,
              __eo_to_smt_updater_rec (SmtTerm.DtSel s d i j) k t u acc ≠
                SmtTerm.DtTester s0 d0 i0 :=
          eo_to_smt_updater_rec_ne_dt_tester s d i j k t u acc hAccTester
        have hArg :
            __smtx_typeof
                (native_ite (native_nateq j k) u
                  (SmtTerm.Apply (SmtTerm.DtSel s d i k) t)) ≠
              SmtType.None :=
          smtx_apply_arg_non_none_of_non_none
            (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j) k t u acc)
            (native_ite (native_nateq j k) u (SmtTerm.Apply (SmtTerm.DtSel s d i k) t))
            hRecSel hRecTester
            (by
              simpa [__eo_to_smt_updater_rec] using hNN)
        simpa [native_ite, hEq] using hArg
      · have hIdxK :
            native_zlt (native_nat_to_int j) (native_nat_to_int k) = true := by
          have hjk : j < k := by
            have hIdx' := hIdx
            unfold native_zlt at hIdx'
            have hjInt := of_decide_eq_true hIdx'
            unfold native_nat_to_int at hjInt
            have hjSucc : j < Nat.succ k := Int.ofNat_lt.mp hjInt
            have hne : j ≠ k := by
              intro h
              subst j
              simp [native_nateq, Smtm.native_nateq] at hEq
            exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hjSucc) hne
          have hjkInt : (j : Int) < (k : Int) := Int.ofNat_lt.mpr hjk
          simpa [native_zlt, SmtEval.native_zlt, native_nat_to_int,
            Smtm.native_nat_to_int] using hjkInt
        have hRecNN :
            __smtx_typeof
                (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j) k t u acc) ≠
              SmtType.None :=
          smtx_apply_head_non_none_of_non_none
            (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j) k t u acc)
            (native_ite (native_nateq j k) u (SmtTerm.Apply (SmtTerm.DtSel s d i k) t))
            (eo_to_smt_updater_rec_ne_dt_sel s d i j k t u acc hAccSel)
            (eo_to_smt_updater_rec_ne_dt_tester s d i j k t u acc hAccTester)
            (by
              simpa [__eo_to_smt_updater_rec] using hNN)
        exact ih acc hAccSel hAccTester hIdxK hRecNN

theorem eo_to_smt_updater_rec_type_of_non_none
    (s : native_String) (d : SmtDatatypeDecl) (i j n : native_Nat) (t u : SmtTerm)
    (hNN :
      __smtx_typeof
          (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j) n t u
            (SmtTerm.DtCons s d i)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j) n t u
          (SmtTerm.DtCons s d i)) =
      dt_cons_applied_type_rec s d
        (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i n := by
  induction n with
  | zero =>
      let raw :=
        __smtx_typeof_dt_cons_rec (SmtType.Datatype s d)
          (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
      have hGuardNN :
          __smtx_typeof_guard_wf (SmtType.Datatype s d) raw ≠
            SmtType.None := by
        simpa [__eo_to_smt_updater_rec, Smtm.typeof_dt_cons_eq, raw] using hNN
      have hGuard :
          __smtx_typeof_guard_wf (SmtType.Datatype s d) raw = raw :=
        smtx_typeof_guard_wf_of_non_none (SmtType.Datatype s d) raw hGuardNN
      simpa [__eo_to_smt_updater_rec, Smtm.typeof_dt_cons_eq, raw,
        dt_cons_applied_type_rec, typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec]
        using hGuard
  | succ k ih =>
      let recTerm :=
        __eo_to_smt_updater_rec (SmtTerm.DtSel s d i j) k t u
          (SmtTerm.DtCons s d i)
      let argTerm :=
        native_ite (native_nateq j k) u (SmtTerm.Apply (SmtTerm.DtSel s d i k) t)
      have hTermNN :
          __smtx_typeof (SmtTerm.Apply recTerm argTerm) ≠ SmtType.None := by
        simpa [__eo_to_smt_updater_rec, recTerm, argTerm] using hNN
      have hRecSel :
          ∀ s0 d0 i0 j0, recTerm ≠ SmtTerm.DtSel s0 d0 i0 j0 := by
        exact eo_to_smt_updater_rec_ne_dt_sel s d i j k t u
          (SmtTerm.DtCons s d i) (by intro s0 d0 i0 j0 h; cases h)
      have hRecTester :
          ∀ s0 d0 i0, recTerm ≠ SmtTerm.DtTester s0 d0 i0 := by
        exact eo_to_smt_updater_rec_ne_dt_tester s d i j k t u
          (SmtTerm.DtCons s d i) (by intro s0 d0 i0 h; cases h)
      have hGeneric : generic_apply_type recTerm argTerm :=
        generic_apply_type_of_non_special_head recTerm argTerm hRecSel hRecTester
      have hApplyNN :
          __smtx_typeof_apply (__smtx_typeof recTerm) (__smtx_typeof argTerm) ≠
            SmtType.None := by
        unfold generic_apply_type at hGeneric
        rw [hGeneric] at hTermNN
        exact hTermNN
      have hRecNN : __smtx_typeof recTerm ≠ SmtType.None := by
        exact smtx_apply_head_non_none_of_non_none recTerm argTerm hRecSel hRecTester hTermNN
      have hRecTy :
          __smtx_typeof recTerm =
            dt_cons_applied_type_rec s d
              (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i k := by
        simpa [recTerm] using ih hRecNN
      rcases typeof_apply_non_none_cases hApplyNN with
        ⟨A, B, hHead, hArg, hA, _hB⟩
      have hlt :
          k < __smtx_dt_num_sels
            (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i := by
        rcases hHead with hHead | hHead
        · have hArgs := congrArg dt_cons_type_num_args hHead
          rw [hRecTy, dt_cons_type_num_args_dt_cons_applied_type_rec] at hArgs
          simp [dt_cons_type_num_args] at hArgs
          omega
        · have hArgs := congrArg dt_cons_type_num_args hHead
          rw [hRecTy, dt_cons_type_num_args_dt_cons_applied_type_rec] at hArgs
          simp [dt_cons_type_num_args] at hArgs
          omega
      let R := __smtx_ret_typeof_sel_rec
        (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i k
      let Rest :=
        dt_cons_applied_type_rec s d
          (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i (Nat.succ k)
      have hStep :
          dt_cons_applied_type_rec s d
              (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i k =
            SmtType.DtcAppType R Rest := by
        simpa [R, Rest] using
          dt_cons_applied_type_rec_step s d
            (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i k hlt
      have hArgR : __smtx_typeof argTerm = R := by
        rcases hHead with hHead | hHead
        · have hBad :
            SmtType.DtcAppType R Rest = SmtType.FunType A B := by
            exact (hRecTy.trans hStep).symm.trans hHead
          cases hBad
        · have hCmp :
              SmtType.DtcAppType R Rest = SmtType.DtcAppType A B := by
            exact (hRecTy.trans hStep).symm.trans hHead
          injection hCmp with hAeq _hBeq
          exact hArg.trans hAeq.symm
      have hRNN : R ≠ SmtType.None := by
        rw [← hArgR]
        exact smtx_apply_arg_non_none_of_non_none recTerm argTerm hRecSel hRecTester hTermNN
      have hApplyTy :
          __smtx_typeof (SmtTerm.Apply recTerm argTerm) = Rest := by
        rw [hGeneric]
        exact smtx_typeof_apply_of_head_cases (Or.inr (hRecTy.trans hStep)) hArgR hRNN
      simpa [__eo_to_smt_updater_rec, recTerm, argTerm, Rest] using hApplyTy

theorem eo_to_smt_updater_rec_update_arg_type_of_non_none
    (s : native_String) (d : SmtDatatypeDecl) (i j n : native_Nat) (t u : SmtTerm)
    (hIdx : native_zlt (native_nat_to_int j) (native_nat_to_int n) = true)
    (hNN :
      __smtx_typeof
          (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j) n t u
            (SmtTerm.DtCons s d i)) ≠
        SmtType.None) :
    __smtx_typeof u = __smtx_ret_typeof_sel s d i j := by
  induction n with
  | zero =>
      have hIdx' := hIdx
      unfold native_zlt at hIdx'
      have hjInt := of_decide_eq_true hIdx'
      unfold native_nat_to_int at hjInt
      have hj : j < Nat.zero := Int.ofNat_lt.mp hjInt
      exact (Nat.not_lt_zero j hj).elim
  | succ k ih =>
      let recTerm :=
        __eo_to_smt_updater_rec (SmtTerm.DtSel s d i j) k t u
          (SmtTerm.DtCons s d i)
      let argTerm :=
        native_ite (native_nateq j k) u (SmtTerm.Apply (SmtTerm.DtSel s d i k) t)
      have hTermNN :
          __smtx_typeof (SmtTerm.Apply recTerm argTerm) ≠ SmtType.None := by
        simpa [__eo_to_smt_updater_rec, recTerm, argTerm] using hNN
      have hRecSel :
          ∀ s0 d0 i0 j0, recTerm ≠ SmtTerm.DtSel s0 d0 i0 j0 := by
        exact eo_to_smt_updater_rec_ne_dt_sel s d i j k t u
          (SmtTerm.DtCons s d i) (by intro s0 d0 i0 j0 h; cases h)
      have hRecTester :
          ∀ s0 d0 i0, recTerm ≠ SmtTerm.DtTester s0 d0 i0 := by
        exact eo_to_smt_updater_rec_ne_dt_tester s d i j k t u
          (SmtTerm.DtCons s d i) (by intro s0 d0 i0 h; cases h)
      by_cases hEq : native_nateq j k = true
      · have hjk : j = k := by
          simpa [native_nateq, Smtm.native_nateq] using hEq
        have hGeneric : generic_apply_type recTerm argTerm :=
          generic_apply_type_of_non_special_head recTerm argTerm hRecSel hRecTester
        have hApplyNN :
            __smtx_typeof_apply (__smtx_typeof recTerm) (__smtx_typeof argTerm) ≠
              SmtType.None := by
          unfold generic_apply_type at hGeneric
          rw [hGeneric] at hTermNN
          exact hTermNN
        have hRecNN : __smtx_typeof recTerm ≠ SmtType.None := by
          exact smtx_apply_head_non_none_of_non_none recTerm argTerm hRecSel hRecTester
            hTermNN
        have hRecTy :
            __smtx_typeof recTerm =
              dt_cons_applied_type_rec s d
                (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i k := by
          exact eo_to_smt_updater_rec_type_of_non_none s d i j k t u hRecNN
        rcases typeof_apply_non_none_cases hApplyNN with
          ⟨A, B, hHead, hArg, _hA, _hB⟩
        have hlt :
            k < __smtx_dt_num_sels
              (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i := by
          rcases hHead with hHead | hHead
          · have hArgs := congrArg dt_cons_type_num_args hHead
            rw [hRecTy, dt_cons_type_num_args_dt_cons_applied_type_rec] at hArgs
            simp [dt_cons_type_num_args] at hArgs
            omega
          · have hArgs := congrArg dt_cons_type_num_args hHead
            rw [hRecTy, dt_cons_type_num_args_dt_cons_applied_type_rec] at hArgs
            simp [dt_cons_type_num_args] at hArgs
            omega
        let R := __smtx_ret_typeof_sel_rec
          (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i k
        let Rest :=
          dt_cons_applied_type_rec s d
            (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i (Nat.succ k)
        have hStep :
            dt_cons_applied_type_rec s d
                (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i k =
              SmtType.DtcAppType R Rest := by
          simpa [R, Rest] using
            dt_cons_applied_type_rec_step s d
              (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i k hlt
        have hArgR : __smtx_typeof argTerm = R := by
          rcases hHead with hHead | hHead
          · have hBad :
              SmtType.DtcAppType R Rest = SmtType.FunType A B := by
              exact (hRecTy.trans hStep).symm.trans hHead
            cases hBad
          · have hCmp :
                SmtType.DtcAppType R Rest = SmtType.DtcAppType A B := by
              exact (hRecTy.trans hStep).symm.trans hHead
            injection hCmp with hAeq _hBeq
            exact hArg.trans hAeq.symm
        have hArgU : argTerm = u := by
          simp [argTerm, native_ite, hEq]
        subst hjk
        simpa [hArgU, R, __smtx_ret_typeof_sel] using hArgR
      · have hIdxK :
            native_zlt (native_nat_to_int j) (native_nat_to_int k) = true := by
          have hjk : j < k := by
            have hIdx' := hIdx
            unfold native_zlt at hIdx'
            have hjInt := of_decide_eq_true hIdx'
            unfold native_nat_to_int at hjInt
            have hjSucc : j < Nat.succ k := Int.ofNat_lt.mp hjInt
            have hne : j ≠ k := by
              intro h
              subst j
              simp [native_nateq, Smtm.native_nateq] at hEq
            exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hjSucc) hne
          have hjkInt : (j : Int) < (k : Int) := Int.ofNat_lt.mpr hjk
          simpa [native_zlt, SmtEval.native_zlt, native_nat_to_int,
            Smtm.native_nat_to_int] using hjkInt
        have hRecNN : __smtx_typeof recTerm ≠ SmtType.None := by
          exact smtx_apply_head_non_none_of_non_none recTerm argTerm hRecSel hRecTester hTermNN
        exact ih hIdxK hRecNN

/-- `update`, reducing the selector head and reusing the EO-side update typing helper. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_update
    (x y z : Term)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update z) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update z) y) x)) := by
  cases hz : __eo_to_smt z
  case DtSel s d i j =>
    let t := Term.Apply (Term.Apply (Term.UOp1 UserOp1.update z) y) x
    have hTranslate :
        __eo_to_smt t =
          __eo_to_smt_updater (SmtTerm.DtSel s d i j) (__eo_to_smt y) (__eo_to_smt x) := by
      change
        __eo_to_smt_updater (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) =
          __eo_to_smt_updater (SmtTerm.DtSel s d i j) (__eo_to_smt y) (__eo_to_smt x)
      rw [hz]
    have hUpdaterNN :
        __smtx_typeof
            (__eo_to_smt_updater (SmtTerm.DtSel s d i j) (__eo_to_smt y) (__eo_to_smt x)) ≠
          SmtType.None := by
      rw [← hTranslate]
      exact hNonNone
    have hIdx :
        native_zlt (native_nat_to_int j)
            (native_nat_to_int (__smtx_dt_num_sels (__smtx_dd_lookup s d) i)) =
          true := by
      exact eo_to_smt_updater_dt_sel_guard_of_non_none
        s d i j (__eo_to_smt y) (__eo_to_smt x) hUpdaterNN
    have hIteNN :
        term_has_non_none_type
          (SmtTerm.ite
            (SmtTerm.Apply (SmtTerm.DtTester s d i) (__eo_to_smt y))
            (__eo_to_smt_updater_rec
              (SmtTerm.DtSel s d i j) (__smtx_dt_num_sels (__smtx_dd_lookup s d) i)
              (__eo_to_smt y)
              (__eo_to_smt x) (SmtTerm.DtCons s d i))
            (__eo_to_smt y)) := by
      unfold term_has_non_none_type
      simpa [__eo_to_smt_updater, native_ite, hIdx] using hUpdaterNN
    rcases ite_args_of_non_none hIteNN with ⟨T, hCond, hThen, hElse, _hT⟩
    have hCondNN :
        term_has_non_none_type
          (SmtTerm.Apply (SmtTerm.DtTester s d i) (__eo_to_smt y)) := by
      unfold term_has_non_none_type
      rw [hCond]
      simp
    have hYTy : __smtx_typeof (__eo_to_smt y) = SmtType.Datatype s d :=
      dt_tester_arg_datatype_of_non_none hCondNN
    have hTTy : T = SmtType.Datatype s d :=
      hElse.symm.trans hYTy
    have hSmt : __smtx_typeof (__eo_to_smt t) = SmtType.Datatype s d := by
      rw [hTranslate, __eo_to_smt_updater]
      simp [native_ite, hIdx]
      rw [typeof_ite_eq, hCond, hThen, hElse, hTTy]
      simp [__smtx_typeof_ite, native_ite, native_Teq]
    have hYNN : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
      rw [hYTy]
      simp
    have hYEo : __eo_to_smt_type (__eo_typeof y) = SmtType.Datatype s d := by
      have h := ihY hYNN
      rw [hYTy] at h
      exact h.symm
    have hXNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      exact eo_to_smt_updater_rec_update_arg_non_none_of_non_none
        s d i j (__smtx_dt_num_sels (__smtx_dd_lookup s d) i)
        (__eo_to_smt y) (__eo_to_smt x)
        (SmtTerm.DtCons s d i)
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
        hIdx
        (by
          rw [hThen]
          exact _hT)
    have hxNonStuck : __eo_typeof x ≠ Term.Stuck :=
      eo_term_ne_stuck_of_smt_type_non_none (__eo_typeof x) (by
        have h := ihX hXNN
        rw [← h]
        exact hXNN)
    have hzNonStuck : __eo_typeof z ≠ Term.Stuck := by
      rcases eo_to_smt_eq_dt_sel_cases z s d i j hz with
        ⟨d0, hd, hzEq, _hReserved⟩ | ⟨z0, hzEq, _hz0⟩
      · subst z
        intro hStuck
        change
          Term.Apply (Term.Apply Term.FunType (Term.DatatypeType s d0))
              (__eo_typeof_dt_sel_return (__eo_dd_resolve s d0) i j) =
            Term.Stuck at hStuck
        cases hStuck
      · subst z
        change SmtTerm._at_purify (__eo_to_smt z0) = SmtTerm.DtSel s d i j at hz
        cases hz
    have hEo :
        __eo_to_smt_type (__eo_typeof t) = SmtType.Datatype s d := by
      have hCore :=
        eo_to_smt_type_typeof_apply_apply_apply_update_of_middle_type
          x y z (__eo_typeof y) hzNonStuck rfl hxNonStuck
      exact hCore.trans hYEo
    exact hSmt.trans hEo.symm
  all_goals
    exact False.elim (hNonNone (by
      change
        __smtx_typeof
            (__eo_to_smt_updater (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) =
          SmtType.None
      rw [hz]
      simp [__eo_to_smt_updater]))

/-- `tuple_update`, reducing the tuple datatype and numeral index cases locally. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_tuple_update
    (x y z : Term)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update z) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update z) y) x)) := by
  cases hTy : __smtx_typeof (__eo_to_smt y)
  case Datatype s d =>
    cases hz : __eo_to_smt z
    case Numeral n =>
      by_cases hs : s = (native_string_lit "@Tuple")
      · subst s
        let t := Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update z) y) x
        have hTranslate :
            __eo_to_smt t =
              __eo_to_smt_tuple_update (SmtType.Datatype (native_string_lit "@Tuple") d)
                (SmtTerm.Numeral n) (__eo_to_smt y) (__eo_to_smt x) := by
          change
            __eo_to_smt_tuple_update (__smtx_typeof (__eo_to_smt y)) (__eo_to_smt z)
                (__eo_to_smt y) (__eo_to_smt x) =
              __eo_to_smt_tuple_update (SmtType.Datatype (native_string_lit "@Tuple") d)
                (SmtTerm.Numeral n) (__eo_to_smt y) (__eo_to_smt x)
          rw [hTy, hz]
        have hTupleNN :
            __smtx_typeof
                (__eo_to_smt_tuple_update (SmtType.Datatype (native_string_lit "@Tuple") d)
                  (SmtTerm.Numeral n) (__eo_to_smt y) (__eo_to_smt x)) ≠
              SmtType.None := by
          rw [← hTranslate]
          exact hNonNone
        have hDecl : ∃ body, d = __eo_to_smt_tuple_decl body := by
          cases d with
          | nil =>
              exfalso
              apply hTupleNN
              simp [__eo_to_smt_tuple_update]
          | cons s2 body rest =>
              cases rest with
              | cons s3 body3 rest3 =>
                  exfalso
                  apply hTupleNN
                  simp [__eo_to_smt_tuple_update]
              | nil =>
                  by_cases hs2 : s2 = native_string_lit "@Tuple"
                  · subst s2
                    exact ⟨body, rfl⟩
                  · exfalso
                    apply hTupleNN
                    simp [__eo_to_smt_tuple_update, hs2, native_streq,
                      native_and, native_ite]
        rcases hDecl with ⟨body, rfl⟩
        let tupleDD := __eo_to_smt_tuple_decl body
        have hGe : native_zleq 0 n = true := by
          cases hTest : native_zleq 0 n
          · simp [__eo_to_smt_tuple_update, __eo_to_smt_tuple_decl,
              hTest, native_streq, native_and, native_ite] at hTupleNN
          · rfl
        have hUpdaterNN :
            __smtx_typeof
                (__eo_to_smt_updater
                  (SmtTerm.DtSel (native_string_lit "@Tuple") tupleDD native_nat_zero (native_int_to_nat n))
                  (__eo_to_smt y) (__eo_to_smt x)) ≠
              SmtType.None := by
          simpa [__eo_to_smt_tuple_update, __eo_to_smt_tuple_decl,
            tupleDD, hGe, native_streq, native_and, native_ite] using hTupleNN
        have hIdx :
            native_zlt
                (native_nat_to_int (native_int_to_nat n))
                (native_nat_to_int
                  (__smtx_dt_num_sels
                    (__smtx_dd_lookup (native_string_lit "@Tuple") tupleDD)
                    native_nat_zero)) =
              true := by
          exact eo_to_smt_updater_dt_sel_guard_of_non_none
            (native_string_lit "@Tuple") tupleDD native_nat_zero (native_int_to_nat n)
            (__eo_to_smt y) (__eo_to_smt x)
            hUpdaterNN
        have hIteNN :
            term_has_non_none_type
              (SmtTerm.ite
                (SmtTerm.Apply (SmtTerm.DtTester (native_string_lit "@Tuple") tupleDD native_nat_zero) (__eo_to_smt y))
                (__eo_to_smt_updater_rec
                  (SmtTerm.DtSel (native_string_lit "@Tuple") tupleDD native_nat_zero (native_int_to_nat n))
                  (__smtx_dt_num_sels
                    (__smtx_dd_lookup (native_string_lit "@Tuple") tupleDD)
                    native_nat_zero) (__eo_to_smt y)
                  (__eo_to_smt x) (SmtTerm.DtCons (native_string_lit "@Tuple") tupleDD native_nat_zero))
                (__eo_to_smt y)) := by
          unfold term_has_non_none_type
          simpa [__eo_to_smt_updater, native_ite, hIdx] using hUpdaterNN
        rcases ite_args_of_non_none hIteNN with ⟨T, hCond, hThen, hElse, _hT⟩
        have hCondNN :
            term_has_non_none_type
              (SmtTerm.Apply (SmtTerm.DtTester (native_string_lit "@Tuple") tupleDD native_nat_zero) (__eo_to_smt y)) := by
          unfold term_has_non_none_type
          rw [hCond]
          simp
        have hYTy : __smtx_typeof (__eo_to_smt y) = SmtType.Datatype (native_string_lit "@Tuple") tupleDD :=
          dt_tester_arg_datatype_of_non_none hCondNN
        have hYNN : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
          rw [hYTy]
          simp
        have hYTypeFromIH :
            __eo_to_smt_type (__eo_typeof y) = SmtType.Datatype (native_string_lit "@Tuple") tupleDD :=
          (ihY hYNN).symm.trans hYTy
        have hYTypeBody :
            __eo_to_smt_type (__eo_typeof y) =
              SmtType.Datatype (native_string_lit "@Tuple")
                (__eo_to_smt_tuple_decl body) := by
          simpa [tupleDD] using hYTypeFromIH
        have hTTy : T = SmtType.Datatype (native_string_lit "@Tuple") tupleDD :=
          hElse.symm.trans hYTy
        have hInnerTy :
            __smtx_typeof
                (__eo_to_smt_updater
                  (SmtTerm.DtSel (native_string_lit "@Tuple") tupleDD native_nat_zero (native_int_to_nat n))
                  (__eo_to_smt y) (__eo_to_smt x)) =
              SmtType.Datatype (native_string_lit "@Tuple") tupleDD := by
          rw [__eo_to_smt_updater]
          simp [native_ite, hIdx]
          rw [typeof_ite_eq, hCond, hThen, hElse, hTTy]
          simp [__smtx_typeof_ite, native_ite, native_Teq]
        have hSmt : __smtx_typeof (__eo_to_smt t) = SmtType.Datatype (native_string_lit "@Tuple") tupleDD := by
          rw [hTranslate]
          simpa [__eo_to_smt_tuple_update, __eo_to_smt_tuple_decl,
            tupleDD, hGe, native_ite, native_and, native_streq,
            SmtEval.native_streq] using hInnerTy
        have hRecNN :
            __smtx_typeof
                (__eo_to_smt_updater_rec
                  (SmtTerm.DtSel (native_string_lit "@Tuple") tupleDD native_nat_zero (native_int_to_nat n))
                  (__smtx_dt_num_sels
                    (__smtx_dd_lookup (native_string_lit "@Tuple") tupleDD)
                    native_nat_zero) (__eo_to_smt y)
                  (__eo_to_smt x)
                  (SmtTerm.DtCons (native_string_lit "@Tuple") tupleDD native_nat_zero)) ≠
              SmtType.None := by
          rw [hThen]
          exact _hT
        have hXRetSmt :
            __smtx_typeof (__eo_to_smt x) =
              __smtx_ret_typeof_sel (native_string_lit "@Tuple") tupleDD native_nat_zero (native_int_to_nat n) :=
          eo_to_smt_updater_rec_update_arg_type_of_non_none
            (native_string_lit "@Tuple") tupleDD native_nat_zero (native_int_to_nat n)
            (__smtx_dt_num_sels
              (__smtx_dd_lookup (native_string_lit "@Tuple") tupleDD)
              native_nat_zero) (__eo_to_smt y) (__eo_to_smt x)
            hIdx hRecNN
        have hXNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
          exact eo_to_smt_updater_rec_update_arg_non_none_of_non_none
            (native_string_lit "@Tuple") tupleDD native_nat_zero (native_int_to_nat n)
            (__smtx_dt_num_sels
              (__smtx_dd_lookup (native_string_lit "@Tuple") tupleDD)
              native_nat_zero) (__eo_to_smt y) (__eo_to_smt x)
            (SmtTerm.DtCons (native_string_lit "@Tuple") tupleDD native_nat_zero)
            (by intro s d i j h; cases h)
            (by intro s d i h; cases h)
            hIdx hRecNN
        have hXEo :
            __eo_to_smt_type (__eo_typeof x) =
              __smtx_ret_typeof_sel (native_string_lit "@Tuple") tupleDD native_nat_zero (native_int_to_nat n) :=
          (ihX hXNN).symm.trans hXRetSmt
        have hYN : z = Term.Numeral n :=
          eo_to_smt_eq_numeral z n hz
        subst z
        have hTupleWf :
            __smtx_type_wf (SmtType.Datatype (native_string_lit "@Tuple") tupleDD) = true :=
          Smtm.smt_datatype_wf_of_non_none_type
            (__eo_to_smt y) (native_string_lit "@Tuple") tupleDD hYTy
        have hYValidTop : eo_type_valid (__eo_typeof y) :=
          eo_type_valid_of_smt_wf (__eo_typeof y) (by
            simpa [hYTypeFromIH] using hTupleWf)
        have hYValidRec : eo_type_valid_rec [] (__eo_typeof y) :=
          eo_type_valid_rec_of_tuple_smt_type hYTypeBody hYValidTop
        have hList :
            __eo_is_list (Term.UOp UserOp.Tuple) (__eo_typeof y) =
              Term.Boolean true :=
          eo_tuple_is_list_true_of_smt_tuple_type hYTypeBody
        have hnNonneg : (0 : Int) ≤ n := by
          simpa [native_zleq, SmtEval.native_zleq] using hGe
        have hNatInt :
            native_nat_to_int (native_int_to_nat n) = n := by
          simp [native_nat_to_int, native_int_to_nat,
            Smtm.native_nat_to_int, SmtEval.native_int_to_nat,
            Int.toNat_of_nonneg hnNonneg]
        have hRetNth :
            __smtx_ret_typeof_sel (native_string_lit "@Tuple") tupleDD native_nat_zero (native_int_to_nat n) =
              __eo_to_smt_type
                (__eo_list_nth (Term.UOp UserOp.Tuple) (__eo_typeof y)
                  (Term.Numeral n)) := by
          simp [__eo_list_nth, __eo_requires, hList, native_ite, native_teq,
            native_not, SmtEval.native_not]
          simpa [hNatInt] using
            smtx_ret_typeof_tuple_sel_eq_eo_list_nth_rec_nat
              (T := __eo_typeof y) (d := body) (j := native_int_to_nat n)
              hYTypeBody hYValidRec
        have hIdxNat :
            native_int_to_nat n < __smtx_dt_num_sels body native_nat_zero := by
          have hIdx' :
              native_zlt (native_nat_to_int (native_int_to_nat n))
                  (native_nat_to_int (__smtx_dt_num_sels body native_nat_zero)) = true := by
            simpa [tupleDD, __eo_to_smt_tuple_decl, __smtx_dd_lookup,
              native_ite, native_streq, SmtEval.native_streq] using hIdx
          unfold native_zlt at hIdx'
          have hIdxInt := of_decide_eq_true hIdx'
          unfold native_nat_to_int at hIdxInt
          exact Int.ofNat_lt.mp hIdxInt
        have hNthValidRec :
            eo_type_valid_rec []
              (__eo_list_nth_rec (__eo_typeof y)
                (Term.Numeral (native_nat_to_int (native_int_to_nat n)))) :=
          eo_type_valid_rec_tuple_list_nth_rec_nat
            (T := __eo_typeof y) (d := body) (j := native_int_to_nat n)
            hYTypeBody hYValidRec hIdxNat
        have hNthValid :
            eo_type_valid_rec []
              (__eo_list_nth (Term.UOp UserOp.Tuple) (__eo_typeof y)
                (Term.Numeral n)) := by
          simp [__eo_list_nth, __eo_requires, hList, native_ite, native_teq,
            native_not, SmtEval.native_not]
          simpa [hNatInt] using hNthValidRec
        have hNthEqX :
            __eo_list_nth (Term.UOp UserOp.Tuple) (__eo_typeof y)
                (Term.Numeral n) =
              __eo_typeof x :=
          eo_to_smt_type_eq_of_valid_rec hNthValid (hRetNth.symm.trans hXEo.symm)
        have hTNN : __eo_to_smt_type (__eo_typeof y) ≠ SmtType.None := by
          rw [hYTypeFromIH]
          simp
        have hRetNN :
            __smtx_ret_typeof_sel (native_string_lit "@Tuple") tupleDD native_nat_zero (native_int_to_nat n) ≠
              SmtType.None := by
          rw [← hXRetSmt]
          exact hXNN
        have hNthNN :
            __eo_to_smt_type
                (__eo_list_nth (Term.UOp UserOp.Tuple) (__eo_typeof y)
                  (Term.Numeral n)) ≠
              SmtType.None := by
          rw [← hRetNth]
          exact hRetNN
        have hEo : __eo_to_smt_type (__eo_typeof t) =
            SmtType.Datatype (native_string_lit "@Tuple") tupleDD := by
          have hCore :=
            eo_to_smt_type_typeof_apply_apply_apply_tuple_update_of_int_list_nth_type
              x y (Term.Numeral n) (__eo_typeof y) rfl rfl hNthEqX.symm
              hTNN hNthNN
          have hCore' :
              __eo_to_smt_type (__eo_typeof t) =
                __eo_to_smt_type (__eo_typeof y) := by
            simpa [t] using hCore
          exact hCore'.trans hYTypeFromIH
        exact hSmt.trans hEo.symm
      · exact False.elim (hNonNone (by
          change
            __smtx_typeof
                (__eo_to_smt_tuple_update (__smtx_typeof (__eo_to_smt y)) (__eo_to_smt z)
                  (__eo_to_smt y) (__eo_to_smt x)) =
              SmtType.None
          rw [hTy, hz]
          cases d with
          | nil => simp [__eo_to_smt_tuple_update]
          | cons s2 body rest =>
              cases rest with
              | nil =>
                  simp [__eo_to_smt_tuple_update, hs, native_streq,
                    native_and, native_ite]
              | cons s3 body3 rest3 => simp [__eo_to_smt_tuple_update]))
    all_goals
      exact False.elim (hNonNone (by
        change
          __smtx_typeof
              (__eo_to_smt_tuple_update (__smtx_typeof (__eo_to_smt y)) (__eo_to_smt z)
                (__eo_to_smt y) (__eo_to_smt x)) =
            SmtType.None
        rw [hTy, hz]
        simp [__eo_to_smt_tuple_update]))
  all_goals
    exact False.elim (hNonNone (by
      change
        __smtx_typeof
            (__eo_to_smt_tuple_update (__smtx_typeof (__eo_to_smt y)) (__eo_to_smt z)
              (__eo_to_smt y) (__eo_to_smt x)) =
          SmtType.None
      rw [hTy]
      simp [__eo_to_smt_tuple_update]))

/-- Dispatches special heads shaped as `(f z) y`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_binary_application_head_obligation
    (f z y x : Term)
    (ihFAll :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply f z) y)) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply f z) y)) =
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply f z) y)) ∧
        eo_type_valid (__eo_typeof (Term.Apply (Term.Apply f z) y)))
    (ihZAll :
      __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z) ∧
        eo_type_valid (__eo_typeof z))
    (ihYAll :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y) ∧
        eo_type_valid (__eo_typeof y))
    (ihXAll :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) ∧
        eo_type_valid (__eo_typeof x))
    (ihBelowAll :
      ∀ term,
        sizeOf term < sizeOf (Term.Apply (Term.Apply (Term.Apply f z) y) x) ->
        __smtx_typeof (__eo_to_smt term) ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt term) = __eo_to_smt_type (__eo_typeof term) ∧
          eo_type_valid (__eo_typeof term)) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply f z) y) x)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply f z) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply f z) y) x)) := by
  intro hNonNone
  let ihF := fun hNN => (ihFAll hNN).1
  let ihZ := fun hNN => (ihZAll hNN).1
  let ihY := fun hNN => (ihYAll hNN).1
  let ihX := fun hNN => (ihXAll hNN).1
  cases f
  case UOp op =>
    cases op
    case ite =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_ite_from_ih
        x y z ihZ ihYAll ihX hNonNone
    case bvite =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_bvite_from_ih
        x y z ihZ ihYAll ihX hNonNone
    case str_substr =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_str_substr_from_ih
        x y z ihZ ihY ihX hNonNone
    case str_indexof =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_str_indexof_from_ih
        x y z ihZ ihY ihX hNonNone
    case str_update =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_str_update_from_ih
        x y z ihZ ihY ihX hNonNone
    case str_replace =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_seq_triop
        UserOp.str_replace SmtTerm.str_replace x y z ihZ ihY ihX (by rfl)
        (typeof_str_replace_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x))
        (fun {T} hZ hY hX hT =>
          eo_to_smt_type_typeof_apply_apply_apply_str_replace_of_seq
            x y z T hZ hY hX hT)
        hNonNone
    case str_replace_all =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_seq_triop
        UserOp.str_replace_all SmtTerm.str_replace_all x y z ihZ ihY ihX (by rfl)
        (typeof_str_replace_all_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x))
        (fun {T} hZ hY hX hT =>
          eo_to_smt_type_typeof_apply_apply_apply_str_replace_all_of_seq
            x y z T hZ hY hX hT)
        hNonNone
    case str_replace_re =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_str_replace_re_like
        UserOp.str_replace_re SmtTerm.str_replace_re x y z (by rfl)
        (typeof_str_replace_re_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x))
        (fun hZ hY hX =>
          eo_to_smt_type_typeof_apply_apply_apply_str_replace_re_of_seq_char_reglan
            x y z
            (eo_typeof_eq_seq_char_of_smt_seq_char_from_ih z ihZ hZ)
            (eo_typeof_eq_reglan_of_smt_reglan_from_ih y ihY hY)
            (eo_typeof_eq_seq_char_of_smt_seq_char_from_ih x ihX hX))
        hNonNone
    case str_replace_re_all =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_str_replace_re_like
        UserOp.str_replace_re_all SmtTerm.str_replace_re_all x y z (by rfl)
        (typeof_str_replace_re_all_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x))
        (fun hZ hY hX =>
          eo_to_smt_type_typeof_apply_apply_apply_str_replace_re_all_of_seq_char_reglan
            x y z
            (eo_typeof_eq_seq_char_of_smt_seq_char_from_ih z ihZ hZ)
            (eo_typeof_eq_reglan_of_smt_reglan_from_ih y ihY hY)
            (eo_typeof_eq_seq_char_of_smt_seq_char_from_ih x ihX hX))
        hNonNone
    case str_indexof_re =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_str_indexof_re_from_ih
        x y z ihZ ihY ihX hNonNone
    case store =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_store_from_ih
        x y z ihZ ihY ihX hNonNone
    case _at_strings_num_occur =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp._at_strings_num_occur z y x ihFAll ihXAll
        (smtStringsNumOccur SmtTerm.str_replace_all
          (__eo_to_smt z) (__eo_to_smt y))
        (by rfl)
        (by rfl)
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case _at_strings_occur_index_re =>
      exact
        eo_to_smt_typeof_matches_translation_apply_apply_apply_at_strings_occur_index_re
          x y z ihZ ihY ihX hNonNone
    case or =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.or z y x ihFAll ihXAll
        (SmtTerm.or (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case and =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.and z y x ihFAll ihXAll
        (SmtTerm.and (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case imp =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.imp z y x ihFAll ihXAll
        (SmtTerm.imp (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case xor =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.xor z y x ihFAll ihXAll
        (SmtTerm.xor (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case eq =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.eq z y x ihFAll ihXAll
        (SmtTerm.eq (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case plus =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.plus z y x ihFAll ihXAll
        (SmtTerm.plus (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case neg =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.neg z y x ihFAll ihXAll
        (SmtTerm.neg (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case mult =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.mult z y x ihFAll ihXAll
        (SmtTerm.mult (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case lt =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.lt z y x ihFAll ihXAll
        (SmtTerm.lt (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case leq =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.leq z y x ihFAll ihXAll
        (SmtTerm.leq (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case gt =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.gt z y x ihFAll ihXAll
        (SmtTerm.gt (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case geq =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.geq z y x ihFAll ihXAll
        (SmtTerm.geq (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case div =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.div z y x ihFAll ihXAll
        (SmtTerm.div (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case mod =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.mod z y x ihFAll ihXAll
        (SmtTerm.mod (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case divisible =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.divisible z y x ihFAll ihXAll
        (SmtTerm.divisible (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case div_total =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.div_total z y x ihFAll ihXAll
        (SmtTerm.div_total (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case mod_total =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.mod_total z y x ihFAll ihXAll
        (SmtTerm.mod_total (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case concat =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.concat z y x ihFAll ihXAll
        (SmtTerm.concat (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvand =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvand z y x ihFAll ihXAll
        (SmtTerm.bvand (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvor =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvor z y x ihFAll ihXAll
        (SmtTerm.bvor (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvnand =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvnand z y x ihFAll ihXAll
        (SmtTerm.bvnand (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvnor =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvnor z y x ihFAll ihXAll
        (SmtTerm.bvnor (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvxor =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvxor z y x ihFAll ihXAll
        (SmtTerm.bvxor (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvxnor =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvxnor z y x ihFAll ihXAll
        (SmtTerm.bvxnor (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvcomp =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvcomp z y x ihFAll ihXAll
        (SmtTerm.bvcomp (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvadd =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvadd z y x ihFAll ihXAll
        (SmtTerm.bvadd (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvmul =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvmul z y x ihFAll ihXAll
        (SmtTerm.bvmul (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvudiv =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvudiv z y x ihFAll ihXAll
        (SmtTerm.bvudiv (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvurem =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvurem z y x ihFAll ihXAll
        (SmtTerm.bvurem (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvsub =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvsub z y x ihFAll ihXAll
        (SmtTerm.bvsub (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvsdiv =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvsdiv z y x ihFAll ihXAll
        (SmtTerm.bvsdiv (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvsrem =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvsrem z y x ihFAll ihXAll
        (SmtTerm.bvsrem (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvsmod =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvsmod z y x ihFAll ihXAll
        (SmtTerm.bvsmod (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvult =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvult z y x ihFAll ihXAll
        (SmtTerm.bvult (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvule =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvule z y x ihFAll ihXAll
        (SmtTerm.bvule (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvugt =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvugt z y x ihFAll ihXAll
        (SmtTerm.bvugt (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvuge =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvuge z y x ihFAll ihXAll
        (SmtTerm.bvuge (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvslt =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvslt z y x ihFAll ihXAll
        (SmtTerm.bvslt (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvsle =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvsle z y x ihFAll ihXAll
        (SmtTerm.bvsle (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvsgt =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvsgt z y x ihFAll ihXAll
        (SmtTerm.bvsgt (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvsge =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvsge z y x ihFAll ihXAll
        (SmtTerm.bvsge (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvshl =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvshl z y x ihFAll ihXAll
        (SmtTerm.bvshl (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvlshr =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvlshr z y x ihFAll ihXAll
        (SmtTerm.bvlshr (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvashr =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvashr z y x ihFAll ihXAll
        (SmtTerm.bvashr (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvuaddo =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvuaddo z y x ihFAll ihXAll
        (SmtTerm.bvuaddo (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvsaddo =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvsaddo z y x ihFAll ihXAll
        (SmtTerm.bvsaddo (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvumulo =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvumulo z y x ihFAll ihXAll
        (SmtTerm.bvumulo (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvsmulo =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvsmulo z y x ihFAll ihXAll
        (SmtTerm.bvsmulo (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvusubo =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvusubo z y x ihFAll ihXAll
        (SmtTerm.bvusubo (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvssubo =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvssubo z y x ihFAll ihXAll
        (SmtTerm.bvssubo (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvsdivo =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvsdivo z y x ihFAll ihXAll
        (SmtTerm.bvsdivo (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case select =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.select z y x ihFAll ihXAll
        (SmtTerm.select (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case str_concat =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.str_concat z y x ihFAll ihXAll
        (SmtTerm.str_concat (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case str_contains =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.str_contains z y x ihFAll ihXAll
        (SmtTerm.str_contains (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case str_at =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.str_at z y x ihFAll ihXAll
        (SmtTerm.str_at (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case str_prefixof =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.str_prefixof z y x ihFAll ihXAll
        (SmtTerm.str_prefixof (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case str_suffixof =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.str_suffixof z y x ihFAll ihXAll
        (SmtTerm.str_suffixof (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case str_lt =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.str_lt z y x ihFAll ihXAll
        (SmtTerm.str_lt (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case str_leq =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.str_leq z y x ihFAll ihXAll
        (SmtTerm.str_leq (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case re_range =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.re_range z y x ihFAll ihXAll
        (SmtTerm.re_range (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case re_concat =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.re_concat z y x ihFAll ihXAll
        (SmtTerm.re_concat (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case re_inter =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.re_inter z y x ihFAll ihXAll
        (SmtTerm.re_inter (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case re_union =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.re_union z y x ihFAll ihXAll
        (SmtTerm.re_union (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case re_diff =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.re_diff z y x ihFAll ihXAll
        (SmtTerm.re_diff (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case str_in_re =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.str_in_re z y x ihFAll ihXAll
        (SmtTerm.str_in_re (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case seq_nth =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.seq_nth z y x ihFAll ihXAll
        (SmtTerm.seq_nth (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case _at_from_bools =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp._at_from_bools z y x ihFAll ihXAll
        (SmtTerm.concat
          (__eo_to_smt y)
          (SmtTerm.ite (__eo_to_smt z) (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0))
          )
        (by rfl)
        (by rfl)
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvultbv =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_bv_cmp_to_bv1_applied
        UserOp.bvultbv SmtTerm.bvult x y z (by rfl) hNonNone
    case bvsltbv =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_bv_cmp_to_bv1_applied
        UserOp.bvsltbv SmtTerm.bvslt x y z (by rfl) hNonNone
    case set_union =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.set_union z y x ihFAll ihXAll
        (SmtTerm.set_union (__eo_to_smt z) (__eo_to_smt y)) (by rfl)
        (by rfl)
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case set_inter =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.set_inter z y x ihFAll ihXAll
        (SmtTerm.set_inter (__eo_to_smt z) (__eo_to_smt y)) (by rfl)
        (by rfl)
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case set_minus =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.set_minus z y x ihFAll ihXAll
        (SmtTerm.set_minus (__eo_to_smt z) (__eo_to_smt y)) (by rfl)
        (by rfl)
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case set_choose =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_application_head
        (Term.UOp UserOp.set_choose) z y x ihFAll ihXAll (by rfl) (by rfl) hNonNone
    case set_member =>
      have hHeadTranslate :
          __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_member) z) y) =
            SmtTerm.set_member (__eo_to_smt z) (__eo_to_smt y) := by
        rfl
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_bool_non_special_head_applied
        UserOp.set_member (SmtTerm.set_member (__eo_to_smt z) (__eo_to_smt y)) x y z
        hHeadTranslate
        (by rfl)
        (by
          intro hHeadNN
          rcases set_member_args_of_non_none hHeadNN with ⟨A, hzTy, hyTy⟩
          rw [hHeadTranslate, typeof_set_member_eq]
          simp [__smtx_typeof_set_member, hzTy, hyTy, native_ite, native_Teq])
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
        hNonNone
    case set_subset =>
      have hHeadTranslate :
          __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_subset) z) y) =
            SmtTerm.set_subset (__eo_to_smt z) (__eo_to_smt y) := by
        rfl
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_bool_non_special_head_applied
        UserOp.set_subset (SmtTerm.set_subset (__eo_to_smt z) (__eo_to_smt y)) x y z
        hHeadTranslate
        (by rfl)
        (by
          intro hHeadNN
          rcases set_binop_ret_args_of_non_none
              (op := SmtTerm.set_subset) (T := SmtType.Bool)
              (typeof_set_subset_eq (__eo_to_smt z) (__eo_to_smt y)) hHeadNN with
            ⟨A, hzTy, hyTy⟩
          rw [hHeadTranslate, typeof_set_subset_eq (__eo_to_smt z) (__eo_to_smt y)]
          simp [__smtx_typeof_sets_op_2_ret, hzTy, hyTy, native_ite, native_Teq])
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
        hNonNone
    case qdiv =>
      have hHeadTranslate :
          __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) z) y) =
            SmtTerm.qdiv (__eo_to_smt z) (__eo_to_smt y) := by
        rfl
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_non_function_non_special_head_applied
        UserOp.qdiv (SmtTerm.qdiv (__eo_to_smt z) (__eo_to_smt y)) x y z
        hHeadTranslate
        (by rfl)
        (by
          intro hHeadNN
          rcases arith_binop_ret_args_of_non_none
              (op := SmtTerm.qdiv) (R := SmtType.Real)
              (typeof_qdiv_eq (__eo_to_smt z) (__eo_to_smt y)) hHeadNN with hArgs | hArgs
          · refine ⟨SmtType.Real, ?_, ?_, ?_, ?_⟩
            · rw [hHeadTranslate, typeof_qdiv_eq (__eo_to_smt z) (__eo_to_smt y)]
              simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
            · intro A B h
              cases h
            · intro A B h
              cases h
            · intro A B h
              cases h
          · refine ⟨SmtType.Real, ?_, ?_, ?_, ?_⟩
            · rw [hHeadTranslate, typeof_qdiv_eq (__eo_to_smt z) (__eo_to_smt y)]
              simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
            · intro A B h
              cases h
            · intro A B h
              cases h
            · intro A B h
              cases h)
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
        hNonNone
    case qdiv_total =>
      have hHeadTranslate :
          __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) z) y) =
            SmtTerm.qdiv_total (__eo_to_smt z) (__eo_to_smt y) := by
        rfl
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_non_function_non_special_head_applied
        UserOp.qdiv_total (SmtTerm.qdiv_total (__eo_to_smt z) (__eo_to_smt y)) x y z
        hHeadTranslate
        (by rfl)
        (by
          intro hHeadNN
          rcases arith_binop_ret_args_of_non_none
              (op := SmtTerm.qdiv_total) (R := SmtType.Real)
              (typeof_qdiv_total_eq (__eo_to_smt z) (__eo_to_smt y)) hHeadNN with hArgs | hArgs
          · refine ⟨SmtType.Real, ?_, ?_, ?_, ?_⟩
            · rw [hHeadTranslate, typeof_qdiv_total_eq (__eo_to_smt z) (__eo_to_smt y)]
              simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
            · intro A B h
              cases h
            · intro A B h
              cases h
            · intro A B h
              cases h
          · refine ⟨SmtType.Real, ?_, ?_, ?_, ?_⟩
            · rw [hHeadTranslate, typeof_qdiv_total_eq (__eo_to_smt z) (__eo_to_smt y)]
              simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
            · intro A B h
              cases h
            · intro A B h
              cases h
            · intro A B h
              cases h)
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
        hNonNone
    case _at_strings_occur_index =>
      exact
        eo_to_smt_typeof_matches_translation_apply_apply_apply_at_strings_occur_index
          x y z ihZ ihY ihX hNonNone
    all_goals
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_application_head
        _ z y x ihFAll ihXAll (by rfl) (by rfl) hNonNone
  case Apply g w =>
    cases g
    case UOp op =>
      cases op
      case _at_strings_replace_all_result =>
        let ihW := fun hNN => (ihBelowAll w (by simp; omega) hNN).1
        exact
          eo_to_smt_typeof_matches_translation_apply_apply_apply_apply_at_strings_replace_all_result
            x y z w ihW ihZ ihY ihX hNonNone
      case _at_strings_replace_re_all_result =>
        let ihW := fun hNN => (ihBelowAll w (by simp; omega) hNN).1
        exact
          eo_to_smt_typeof_matches_translation_apply_apply_apply_apply_at_strings_replace_re_all_result
            x y z w ihW ihZ ihY ihX hNonNone
      all_goals
        exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_application_head
          _ z y x ihFAll ihXAll (by rfl) (by rfl) hNonNone
    all_goals
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_application_head
        _ z y x ihFAll ihXAll (by rfl) (by rfl) hNonNone
  all_goals
    exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_application_head
      _ z y x ihFAll ihXAll (by rfl) (by rfl) hNonNone

/-- Handles `(f z) y` heads in the nested-application apply proof. -/
private theorem eo_to_smt_typeof_matches_translation_apply_binary_application_head
    (f z y x : Term)
    (ihF :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply f z) y)) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply f z) y)) =
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply f z) y)) ∧
        eo_type_valid (__eo_typeof (Term.Apply (Term.Apply f z) y)))
    (ihZ :
      __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z) ∧
        eo_type_valid (__eo_typeof z))
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y) ∧
        eo_type_valid (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) ∧
        eo_type_valid (__eo_typeof x))
    (ihBelowAll :
      ∀ term,
        sizeOf term < sizeOf (Term.Apply (Term.Apply (Term.Apply f z) y) x) ->
        __smtx_typeof (__eo_to_smt term) ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt term) = __eo_to_smt_type (__eo_typeof term) ∧
          eo_type_valid (__eo_typeof term)) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply f z) y) x)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply f z) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply f z) y) x)) := by
  intro hNonNone
  exact eo_to_smt_typeof_matches_translation_apply_binary_application_head_obligation
    f z y x ihF ihZ ihY ihX ihBelowAll hNonNone

private theorem eo_to_smt_typeof_matches_translation_apply_apply_head
    (f y x : Term)
    (ihFAll :
      __smtx_typeof (__eo_to_smt (Term.Apply f y)) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt (Term.Apply f y)) =
        __eo_to_smt_type (__eo_typeof (Term.Apply f y)) ∧
        eo_type_valid (__eo_typeof (Term.Apply f y)))
    (ihFArgAll :
      ∀ g z,
        f = Term.Apply g z ->
          __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
          __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z) ∧
            eo_type_valid (__eo_typeof z))
    (ihYAll :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y) ∧
        eo_type_valid (__eo_typeof y))
    (ihXAll :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) ∧
        eo_type_valid (__eo_typeof x))
    (ihBelowAll :
      ∀ term,
        sizeOf term < sizeOf (Term.Apply (Term.Apply f y) x) ->
        __smtx_typeof (__eo_to_smt term) ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt term) = __eo_to_smt_type (__eo_typeof term) ∧
          eo_type_valid (__eo_typeof term)) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply f y) x)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply f y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply f y) x)) := by
  intro hNonNone
  let ihF := fun hNN => (ihFAll hNN).1
  let ihY := fun hNN => (ihYAll hNN).1
  let ihX := fun hNN => (ihXAll hNN).1
  have genericFallback :
      ∀ head : Term,
        (__smtx_typeof (__eo_to_smt head) ≠ SmtType.None ->
          __smtx_typeof (__eo_to_smt head) =
            __eo_to_smt_type (__eo_typeof head) ∧
            eo_type_valid (__eo_typeof head)) ->
        (∀ s d i j, __eo_to_smt head ≠ SmtTerm.DtSel s d i j) ->
        (∀ s d i, __eo_to_smt head ≠ SmtTerm.DtTester s d i) ->
        __eo_to_smt (Term.Apply head x) =
          SmtTerm.Apply (__eo_to_smt head) (__eo_to_smt x) ->
        __eo_typeof (Term.Apply head x) =
          __eo_typeof_apply (__eo_typeof head) (__eo_typeof x) ->
        __smtx_typeof (__eo_to_smt (Term.Apply head x)) ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt (Term.Apply head x)) =
          __eo_to_smt_type (__eo_typeof (Term.Apply head x)) := by
    intro head ihHead hNonSel hNonTester hTranslate hEoApply hNN
    have hGeneric :
        generic_apply_type (__eo_to_smt head) (__eo_to_smt x) :=
      generic_apply_type_of_non_special_head _ _ hNonSel hNonTester
    exact eo_to_smt_typeof_matches_translation_apply_generic_from_ih_of_valid
      head x ihHead ihXAll hGeneric hTranslate hEoApply hNN
  cases f
  case UOp op =>
    exact eo_to_smt_typeof_matches_translation_apply_uop_application_head
      op y x ihFAll ihYAll ihXAll ihBelowAll hNonNone
  case UOp1 op z =>
    cases op
    case update =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_update
        x y z ihY ihX hNonNone
    case tuple_update =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_tuple_update
        x y z ihY ihX hNonNone
    all_goals
      exact genericFallback _ ihFAll
        (by intro s d i j h; exact (eo_to_smt_apply_ne_dt_sel _ y s d i j h).elim)
        (by intro s d i h; exact (eo_to_smt_apply_ne_dt_tester _ y s d i h).elim)
        (by rfl)
        (by rfl)
        hNonNone
  case Apply f z =>
    exact eo_to_smt_typeof_matches_translation_apply_binary_application_head f z y x ihFAll
      (ihFArgAll f z rfl) ihYAll ihXAll ihBelowAll hNonNone
  case FunType =>
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.Apply Term.FunType y) x) =
          SmtTerm.Apply (__eo_to_smt (Term.Apply Term.FunType y)) (__eo_to_smt x) := by
      rfl
    have hHeadTerm :
        __eo_to_smt (Term.Apply Term.FunType y) =
          SmtTerm.Apply SmtTerm.None (__eo_to_smt y) := by
      rfl
    exfalso
    apply hNonNone
    rw [hTranslate, hHeadTerm]
    simp only [__smtx_typeof, __smtx_typeof_apply]
  all_goals
    exact genericFallback _ ihFAll
        (by intro s d i j h; exact (eo_to_smt_apply_ne_dt_sel _ y s d i j h).elim)
        (by intro s d i h; exact (eo_to_smt_apply_ne_dt_tester _ y s d i h).elim)
        (by rfl)
        (by rfl)
        hNonNone

/-- Closes direct `UOp` applications that are unreachable because their SMT type is `none`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_uop_remaining_obligation
    (op : UserOp) (x : Term)
    (hNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp op) x)) = SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp op) x)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp op) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp op) x)) := by
  exact eo_to_smt_typeof_matches_translation_of_smt_none
    (Term.Apply (Term.UOp op) x) hNone

/-- Remaining constructor fallback obligation for heads not handled by specific cases. -/
private theorem eo_to_smt_typeof_matches_translation_apply_constructor_fallback_obligation
    (f x : Term)
    (hNone :
      __smtx_typeof (__eo_to_smt (Term.Apply f x)) = SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply f x)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply f x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply f x)) := by
  exact eo_to_smt_typeof_matches_translation_of_smt_none
    (Term.Apply f x) hNone

theorem eo_to_smt_typeof_matches_translation_apply
    (f x : Term)
    (ihFAll :
      __smtx_typeof (__eo_to_smt f) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt f) = __eo_to_smt_type (__eo_typeof f) ∧
        eo_type_valid (__eo_typeof f))
    (ihXAll :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) ∧
        eo_type_valid (__eo_typeof x))
    (ihUOp1ArgAll :
      ∀ op y,
        f = Term.UOp1 op y ->
          __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
          __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y) ∧
            eo_type_valid (__eo_typeof y))
    (ihApplyArgAll :
      ∀ g y,
        f = Term.Apply g y ->
          __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
          __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y) ∧
            eo_type_valid (__eo_typeof y))
    (ihApplyApplyArgAll :
      ∀ g z y,
        f = Term.Apply (Term.Apply g z) y ->
          __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
          __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z) ∧
            eo_type_valid (__eo_typeof z))
    (ihBelowAll :
      ∀ term,
        sizeOf term < sizeOf (Term.Apply f x) ->
        __smtx_typeof (__eo_to_smt term) ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt term) = __eo_to_smt_type (__eo_typeof term) ∧
          eo_type_valid (__eo_typeof term)) :
    f ≠ Term.UOp UserOp.distinct ->
    __smtx_typeof (__eo_to_smt (Term.Apply f x)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply f x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply f x)) := by
  let ihF := fun hNN => (ihFAll hNN).1
  let ihX := fun hNN => (ihXAll hNN).1
  let ihUOp1Arg := fun op y h hNN => (ihUOp1ArgAll op y h hNN).1
  let ihApplyArg := fun g y h hNN => (ihApplyArgAll g y h hNN).1
  let ihApplyApplyArg := fun g z y h hNN => (ihApplyApplyArgAll g z y h hNN).1
  intro hNotDistinct
  cases f <;> intro hNonNone
  case Var name T =>
    have hGeneric :
        __eo_to_smt (Term.Apply (Term.Var name T) x) =
          SmtTerm.Apply (__eo_to_smt (Term.Var name T)) (__eo_to_smt x) := by
      rfl
    cases hName : name
    case String s =>
      rw [hName] at hGeneric
      rw [hName] at hNonNone
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Var (Term.String s) T) x) =
            SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T)) (__eo_to_smt x) := by
        rw [eo_to_smt_var] at hGeneric
        exact hGeneric
      have hApplyNN :
          __smtx_typeof_apply
              (__smtx_typeof (SmtTerm.Var s (__eo_to_smt_type T)))
              (__smtx_typeof (__eo_to_smt x)) ≠
            SmtType.None := by
        have hGenericApply :
            generic_apply_type
              (SmtTerm.Var s (__eo_to_smt_type T))
              (__eo_to_smt x) := by
          exact generic_apply_type_of_non_special_head _ _
            (by intro s' d i j h; cases h)
            (by intro s' d i h; cases h)
        have hApplyNN' :
            __smtx_typeof
                (SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T)) (__eo_to_smt x)) ≠
              SmtType.None := by
          simpa [hTranslate] using hNonNone
        rw [hGenericApply] at hApplyNN'
        exact hApplyNN'
      rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
      have hVarNN : __smtx_typeof (SmtTerm.Var s (__eo_to_smt_type T)) ≠ SmtType.None := by
        intro hVarNone
        apply hApplyNN
        simp [__smtx_typeof_apply, hVarNone]
      have hHeadTy :
          __smtx_typeof (SmtTerm.Var s (__eo_to_smt_type T)) = __eo_to_smt_type T := by
        simpa using smtx_typeof_var_of_non_none s (__eo_to_smt_type T) hVarNN
      have hT :
          __eo_to_smt_type T = SmtType.FunType A B ∨
            __eo_to_smt_type T = SmtType.DtcAppType A B := by
        rw [← hHeadTy]
        exact hHead
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Var (Term.String s) T) x)) = B := by
        have hGenericApply :
            generic_apply_type
              (SmtTerm.Var s (__eo_to_smt_type T))
              (__eo_to_smt x) := by
          exact generic_apply_type_of_non_special_head _ _
            (by intro s' d i j h; cases h)
            (by intro s' d i h; cases h)
        rw [hTranslate, hGenericApply]
        exact smtx_typeof_apply_of_head_cases hHead hX hA
      have hTWF : __smtx_type_wf (__eo_to_smt_type T) = true :=
        Smtm.smtx_typeof_guard_wf_wf_of_non_none
          (__eo_to_smt_type T) (__eo_to_smt_type T) (by
            simpa [__smtx_typeof] using hVarNN)
      rcases hT with hTFun | hTDtc
      ·
          rcases eo_to_smt_type_eq_fun hTFun with ⟨U, V, hTEq, hU, hV⟩
          have hArgTypeWF : __smtx_type_wf A = true := by
            have h := hTWF
            rw [hTFun] at h
            exact (fun_type_wf_components_of_wf h).1
          have hArgTypeRec : __smtx_type_wf_rec A = true := by
            have h := hTWF
            rw [hTFun] at h
            exact (fun_type_wf_rec_components_of_wf h).1
          have hXTrans : __eo_to_smt_type (__eo_typeof x) = A :=
            eo_to_smt_type_typeof_of_smt_type_from_ih x ihX hX hA
          have hxEo : __eo_typeof x = U :=
            eo_to_smt_type_injective_of_type_wf_rec hXTrans hU hArgTypeRec
          have hUNonNone : __eo_to_smt_type U ≠ SmtType.None := by
            rw [hU]
            exact hA
          have hEo :
              __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Var (Term.String s) T) x)) =
                B :=
            (eo_to_smt_type_typeof_apply_var_of_fun_like
              x T U V s (Or.inl hTEq) hxEo hUNonNone).trans hV
          exact hSmt.trans hEo.symm
      · have hBad := hTWF
        rw [hTDtc] at hBad
        simp [__smtx_type_wf, __smtx_type_wf_rec, native_and] at hBad
    all_goals
      have hVarNone : __eo_to_smt (Term.Var name T) = SmtTerm.None := by
        rw [hName]
        rfl
      apply False.elim
      apply hNonNone
      simpa [hGeneric, hVarNone] using typeof_apply_none_eq (__eo_to_smt x)
  case DtCons s d i =>
    have hReserved : __eo_reserved_datatype_name s = false := by
      cases hRes : __eo_reserved_datatype_name s
      · rfl
      · exfalso
        apply hNonNone
        have hTranslateNone :
            __eo_to_smt (Term.Apply (Term.DtCons s d i) x) =
              SmtTerm.Apply SmtTerm.None (__eo_to_smt x) := by
          change SmtTerm.Apply (__eo_to_smt (Term.DtCons s d i)) (__eo_to_smt x) =
            SmtTerm.Apply SmtTerm.None (__eo_to_smt x)
          simp [eo_to_smt_term_dt_cons, native_ite, hRes]
        rw [hTranslateNone]
        exact typeof_apply_none_eq (__eo_to_smt x)
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.DtCons s d i) x) =
          SmtTerm.Apply (SmtTerm.DtCons s (__eo_to_smt_datatype_decl d) i) (__eo_to_smt x) := by
      have hGeneric :
          __eo_to_smt (Term.Apply (Term.DtCons s d i) x) =
            SmtTerm.Apply (__eo_to_smt (Term.DtCons s d i)) (__eo_to_smt x) := by
        rfl
      simpa [eo_to_smt_term_dt_cons, native_ite, hReserved] using hGeneric
    have hApplyNN :
        __smtx_typeof_apply
            (__smtx_typeof (SmtTerm.DtCons s (__eo_to_smt_datatype_decl d) i))
            (__smtx_typeof (__eo_to_smt x)) ≠
          SmtType.None := by
      have hGenericApply :
          generic_apply_type
            (SmtTerm.DtCons s (__eo_to_smt_datatype_decl d) i)
            (__eo_to_smt x) := by
        exact generic_apply_type_of_non_special_head _ _
          (by intro s' d' i' j h; cases h)
          (by intro s' d' i' h; cases h)
      have hApplyNN' :
          __smtx_typeof
              (SmtTerm.Apply (SmtTerm.DtCons s (__eo_to_smt_datatype_decl d) i) (__eo_to_smt x)) ≠
            SmtType.None := by
        simpa [hTranslate] using hNonNone
      rw [hGenericApply] at hApplyNN'
      exact hApplyNN'
    rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.DtCons s d i) x)) = B := by
      have hGenericApply :
          generic_apply_type
            (SmtTerm.DtCons s (__eo_to_smt_datatype_decl d) i)
            (__eo_to_smt x) := by
        exact generic_apply_type_of_non_special_head _ _
          (by intro s' d' i' j h; cases h)
          (by intro s' d' i' h; cases h)
      rw [hTranslate, hGenericApply]
      exact smtx_typeof_apply_of_head_cases hHead hX hA
    exact hSmt.trans
      (eo_to_smt_type_typeof_apply_dt_cons_of_smt_apply_from_ih
        x s d i A B ihX hReserved hHead hX hA hB).symm
  case DtSel s d i j =>
    have hReserved : __eo_reserved_datatype_name s = false := by
      cases hRes : __eo_reserved_datatype_name s
      · rfl
      · exfalso
        apply hNonNone
        have hTranslateNone :
            __eo_to_smt (Term.Apply (Term.DtSel s d i j) x) =
              SmtTerm.Apply SmtTerm.None (__eo_to_smt x) := by
          change SmtTerm.Apply (__eo_to_smt (Term.DtSel s d i j)) (__eo_to_smt x) =
            SmtTerm.Apply SmtTerm.None (__eo_to_smt x)
          simp [eo_to_smt_term_dt_sel, native_ite, hRes]
        rw [hTranslateNone]
        exact typeof_apply_none_eq (__eo_to_smt x)
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.DtSel s d i j) x) =
          SmtTerm.Apply (SmtTerm.DtSel s (__eo_to_smt_datatype_decl d) i j) (__eo_to_smt x) := by
      have hGeneric :
          __eo_to_smt (Term.Apply (Term.DtSel s d i j) x) =
            SmtTerm.Apply (__eo_to_smt (Term.DtSel s d i j)) (__eo_to_smt x) := by
        rfl
      simpa [eo_to_smt_term_dt_sel, native_ite, hReserved] using hGeneric
    have hApplyNN :
        term_has_non_none_type
          (SmtTerm.Apply (SmtTerm.DtSel s (__eo_to_smt_datatype_decl d) i j) (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg :
        __smtx_typeof (__eo_to_smt x) = SmtType.Datatype s (__eo_to_smt_datatype_decl d) :=
      dt_sel_arg_datatype_of_non_none hApplyNN
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.DtSel s d i j) x)) =
          __smtx_ret_typeof_sel s (__eo_to_smt_datatype_decl d) i j := by
      rw [hTranslate]
      exact dt_sel_term_typeof_of_non_none hApplyNN
    exact hSmt.trans
      (eo_to_smt_type_typeof_apply_dt_sel_of_smt_datatype_from_ih
        x s d i j ihX hReserved hArg hApplyNN).symm
  case UConst i T =>
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.UConst i T) x) =
          SmtTerm.Apply (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T)) (__eo_to_smt x) := by
      have hGeneric :
          __eo_to_smt (Term.Apply (Term.UConst i T) x) =
            SmtTerm.Apply (__eo_to_smt (Term.UConst i T)) (__eo_to_smt x) := by
        rfl
      rw [eo_to_smt_uconst] at hGeneric
      exact hGeneric
    have hApplyNN :
        __smtx_typeof_apply
            (__smtx_typeof (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T)))
            (__smtx_typeof (__eo_to_smt x)) ≠
          SmtType.None := by
      have hGenericApply :
          generic_apply_type
            (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
            (__eo_to_smt x) := by
        exact generic_apply_type_of_non_special_head _ _
          (by intro s' d i' j h; cases h)
          (by intro s' d i' h; cases h)
      have hApplyNN' :
          __smtx_typeof
              (SmtTerm.Apply (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
                (__eo_to_smt x)) ≠
            SmtType.None := by
        simpa [hTranslate] using hNonNone
      rw [hGenericApply] at hApplyNN'
      exact hApplyNN'
    rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
    have hUConstNN :
        __smtx_typeof (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T)) ≠ SmtType.None := by
      intro hUConstNone
      apply hApplyNN
      simp [__smtx_typeof_apply, hUConstNone]
    have hHeadTy :
        __smtx_typeof (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T)) =
          __eo_to_smt_type T := by
      simpa using
        smtx_typeof_uconst_of_non_none (native_uconst_id i) (__eo_to_smt_type T) hUConstNN
    have hT :
        __eo_to_smt_type T = SmtType.FunType A B ∨
          __eo_to_smt_type T = SmtType.DtcAppType A B := by
      rw [← hHeadTy]
      exact hHead
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.UConst i T) x)) = B := by
      have hGenericApply :
          generic_apply_type
            (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
            (__eo_to_smt x) := by
        exact generic_apply_type_of_non_special_head _ _
          (by intro s' d i' j h; cases h)
          (by intro s' d i' h; cases h)
      rw [hTranslate, hGenericApply]
      exact smtx_typeof_apply_of_head_cases hHead hX hA
    have hTWF : __smtx_type_wf (__eo_to_smt_type T) = true :=
      Smtm.smtx_typeof_guard_wf_wf_of_non_none
        (__eo_to_smt_type T) (__eo_to_smt_type T) (by
          simpa [__smtx_typeof] using hUConstNN)
    rcases hT with hTFun | hTDtc
    ·
        rcases eo_to_smt_type_eq_fun hTFun with ⟨U, V, hTEq, hU, hV⟩
        have hArgTypeWF : __smtx_type_wf A = true := by
          have h := hTWF
          rw [hTFun] at h
          exact (fun_type_wf_components_of_wf h).1
        have hArgTypeRec : __smtx_type_wf_rec A = true := by
          have h := hTWF
          rw [hTFun] at h
          exact (fun_type_wf_rec_components_of_wf h).1
        have hXTrans : __eo_to_smt_type (__eo_typeof x) = A :=
          eo_to_smt_type_typeof_of_smt_type_from_ih x ihX hX hA
        have hxEo : __eo_typeof x = U :=
          eo_to_smt_type_injective_of_type_wf_rec hXTrans hU hArgTypeRec
        have hUNonNone : __eo_to_smt_type U ≠ SmtType.None := by
          rw [hU]
          exact hA
        have hEo :
            __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UConst i T) x)) = B :=
          (eo_to_smt_type_typeof_apply_uconst_of_fun_like
            x T U V i (Or.inl hTEq) hxEo hUNonNone).trans hV
        exact hSmt.trans hEo.symm
    · have hBad := hTWF
      rw [hTDtc] at hBad
      simp [__smtx_type_wf, __smtx_type_wf_rec, native_and] at hBad
  case Apply f y =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_head f y x ihFAll
      (fun g z h => ihApplyApplyArgAll g z y (by rw [h]))
      (ihApplyArgAll f y rfl) ihXAll ihBelowAll hNonNone
  case UOp1 op y =>
    cases op
    case «repeat» =>
      exact eo_to_smt_typeof_matches_translation_apply_repeat x y ihX hNonNone
    case zero_extend =>
      exact eo_to_smt_typeof_matches_translation_apply_zero_extend x y ihX hNonNone
    case sign_extend =>
      exact eo_to_smt_typeof_matches_translation_apply_sign_extend x y ihX hNonNone
    case rotate_left =>
      exact eo_to_smt_typeof_matches_translation_apply_rotate_left x y ihX hNonNone
    case rotate_right =>
      exact eo_to_smt_typeof_matches_translation_apply_rotate_right x y ihX hNonNone
    case re_exp =>
      exact eo_to_smt_typeof_matches_translation_apply_re_exp x y ihX hNonNone
    case _at_bit =>
      exact eo_to_smt_typeof_matches_translation_apply_at_bit x y ihX hNonNone
    case int_to_bv =>
      exact eo_to_smt_typeof_matches_translation_apply_int_to_bv x y ihX hNonNone
    case update =>
      exfalso
      apply hNonNone
      change __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) = SmtType.None
      exact typeof_apply_none_eq (__eo_to_smt x)
    case tuple_update =>
      exfalso
      apply hNonNone
      change __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) = SmtType.None
      exact typeof_apply_none_eq (__eo_to_smt x)
    case is =>
      exact eo_to_smt_typeof_matches_translation_apply_is x y
        (ihUOp1Arg UserOp1.is y rfl) ihX hNonNone
    case tuple_select =>
      exact eo_to_smt_typeof_matches_translation_apply_tuple_select x y ihX hNonNone
    case seq_empty =>
      exfalso
      apply hNonNone
      change
        __smtx_typeof
            (SmtTerm.Apply (__eo_to_smt_seq_empty (__eo_to_smt_type y)) (__eo_to_smt x)) =
          SmtType.None
      exact typeof_apply_eo_to_smt_seq_empty_eq_none (__eo_to_smt_type y) (__eo_to_smt x)
    case set_empty =>
      exfalso
      apply hNonNone
      change
        __smtx_typeof
            (SmtTerm.Apply (__eo_to_smt_set_empty (__eo_to_smt_type y)) (__eo_to_smt x)) =
          SmtType.None
      exact typeof_apply_eo_to_smt_set_empty_eq_none (__eo_to_smt_type y) (__eo_to_smt x)
  case UOp2 op y z =>
    cases op
    case extract =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_extract x z y ihX hNonNone
    case re_loop =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_re_loop x z y ihX hNonNone
    case _at_const =>
      cases hValid : __eo_to_smt_nat_is_valid y
      case false =>
        exfalso
        apply hNonNone
        have hNone : __eo_to_smt (Term.UOp2 UserOp2._at_const y z) = SmtTerm.None :=
          eo_to_smt_at_const_of_invalid hValid
        change
          __smtx_typeof
              (SmtTerm.Apply (__eo_to_smt (Term.UOp2 UserOp2._at_const y z))
                (__eo_to_smt x)) =
            SmtType.None
        rw [hNone]
        exact typeof_apply_none_eq (__eo_to_smt x)
      case true =>
        have hHeadTrans :
            __eo_to_smt (Term.UOp2 UserOp2._at_const y z) =
              SmtTerm.UConst (native_const_id (__eo_to_smt_nat y)) (__eo_to_smt_type z) :=
          eo_to_smt_at_const_of_valid hValid
        have hTranslate :
            __eo_to_smt (Term.Apply (Term.UOp2 UserOp2._at_const y z) x) =
              SmtTerm.Apply
                (SmtTerm.UConst (native_const_id (__eo_to_smt_nat y)) (__eo_to_smt_type z))
                (__eo_to_smt x) := by
          have hGeneric :
              __eo_to_smt (Term.Apply (Term.UOp2 UserOp2._at_const y z) x) =
                SmtTerm.Apply (__eo_to_smt (Term.UOp2 UserOp2._at_const y z))
                  (__eo_to_smt x) := by
            rfl
          rw [hHeadTrans] at hGeneric
          exact hGeneric
        have hApplyNN :
            __smtx_typeof_apply
                (__smtx_typeof
                  (SmtTerm.UConst (native_const_id (__eo_to_smt_nat y))
                    (__eo_to_smt_type z)))
                (__smtx_typeof (__eo_to_smt x)) ≠
              SmtType.None := by
          have hGenericApply :
              generic_apply_type
                (SmtTerm.UConst (native_const_id (__eo_to_smt_nat y))
                  (__eo_to_smt_type z))
                (__eo_to_smt x) := by
            exact generic_apply_type_of_non_special_head _ _
              (by intro s' d i' j h; cases h)
              (by intro s' d i' h; cases h)
          have hApplyNN' :
              __smtx_typeof
                  (SmtTerm.Apply
                    (SmtTerm.UConst (native_const_id (__eo_to_smt_nat y))
                      (__eo_to_smt_type z))
                    (__eo_to_smt x)) ≠
                SmtType.None := by
            simpa [hTranslate] using hNonNone
          rw [hGenericApply] at hApplyNN'
          exact hApplyNN'
        rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
        have hUConstNN :
            __smtx_typeof
                (SmtTerm.UConst (native_const_id (__eo_to_smt_nat y))
                  (__eo_to_smt_type z)) ≠
              SmtType.None := by
          intro hUConstNone
          apply hApplyNN
          simp [__smtx_typeof_apply, hUConstNone]
        have hHeadTy :
            __smtx_typeof
                (SmtTerm.UConst (native_const_id (__eo_to_smt_nat y))
                  (__eo_to_smt_type z)) =
              __eo_to_smt_type z := by
          simpa using
            smtx_typeof_uconst_of_non_none (native_const_id (__eo_to_smt_nat y))
              (__eo_to_smt_type z) hUConstNN
        have hT :
            __eo_to_smt_type z = SmtType.FunType A B ∨
              __eo_to_smt_type z = SmtType.DtcAppType A B := by
          rw [← hHeadTy]
          exact hHead
        have hSmt :
            __smtx_typeof
                (__eo_to_smt (Term.Apply (Term.UOp2 UserOp2._at_const y z) x)) = B := by
          have hGenericApply :
              generic_apply_type
                (SmtTerm.UConst (native_const_id (__eo_to_smt_nat y))
                  (__eo_to_smt_type z))
                (__eo_to_smt x) := by
            exact generic_apply_type_of_non_special_head _ _
              (by intro s' d i' j h; cases h)
              (by intro s' d i' h; cases h)
          rw [hTranslate, hGenericApply]
          exact smtx_typeof_apply_of_head_cases hHead hX hA
        have hTWF : __smtx_type_wf (__eo_to_smt_type z) = true :=
          Smtm.smtx_typeof_guard_wf_wf_of_non_none
            (__eo_to_smt_type z) (__eo_to_smt_type z) (by
              simpa [__smtx_typeof] using hUConstNN)
        have hzType : __eo_typeof z = Term.Type :=
          eo_typeof_type_of_smt_type_wf z hTWF
        have hTypeofHead : __eo_typeof (Term.UOp2 UserOp2._at_const y z) = z :=
          eo_typeof_at_const hValid hzType
        rcases hT with hTFun | hTDtc
        · rcases eo_to_smt_type_eq_fun hTFun with ⟨U, V, hTEq, hU, hV⟩
          have hArgTypeRec : __smtx_type_wf_rec A = true := by
            have h := hTWF
            rw [hTFun] at h
            exact (fun_type_wf_rec_components_of_wf h).1
          have hXTrans : __eo_to_smt_type (__eo_typeof x) = A :=
            eo_to_smt_type_typeof_of_smt_type_from_ih x ihX hX hA
          have hxEo : __eo_typeof x = U :=
            eo_to_smt_type_injective_of_type_wf_rec hXTrans hU hArgTypeRec
          have hUNonNone : __eo_to_smt_type U ≠ SmtType.None := by
            rw [hU]
            exact hA
          have hEo :
              __eo_to_smt_type
                  (__eo_typeof (Term.Apply (Term.UOp2 UserOp2._at_const y z) x)) = B := by
            refine Eq.trans ?_ hV
            apply eo_to_smt_type_typeof_apply_of_fun_like
              (f := Term.UOp2 UserOp2._at_const y z) (T := U) (U := V)
            · rfl
            · rw [hTypeofHead]
              exact Or.inl hTEq
            · exact hxEo
            · exact hUNonNone
          exact hSmt.trans hEo.symm
        · have hBad := hTWF
          rw [hTDtc] at hBad
          simp [__smtx_type_wf, __smtx_type_wf_rec, native_and] at hBad
    case _at_quantifiers_skolemize =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term._at_quantifiers_skolemize y z) x) =
            SmtTerm.Apply
              (__eo_to_smt (Term._at_quantifiers_skolemize y z)) (__eo_to_smt x) := by
        rfl
      have hGeneric :
          generic_apply_type
            (__eo_to_smt (Term._at_quantifiers_skolemize y z)) (__eo_to_smt x) := by
        exact generic_apply_type_of_non_special_head _ _
          (eo_to_smt_quant_skolemize_top_ne_dt_sel y z)
          (eo_to_smt_quant_skolemize_top_ne_dt_tester y z)
      have hApplyNN :
          __smtx_typeof_apply
              (__smtx_typeof (__eo_to_smt (Term._at_quantifiers_skolemize y z)))
              (__smtx_typeof (__eo_to_smt x)) ≠ SmtType.None := by
        have hApplyNN' :
            __smtx_typeof
                (SmtTerm.Apply
                  (__eo_to_smt (Term._at_quantifiers_skolemize y z))
                  (__eo_to_smt x)) ≠ SmtType.None := by
          simpa [hTranslate] using hNonNone
        rw [hGeneric] at hApplyNN'
        exact hApplyNN'
      rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, _hB⟩
      have hSmt :
          __smtx_typeof
              (__eo_to_smt (Term.Apply (Term._at_quantifiers_skolemize y z) x)) =
            B := by
        rw [hTranslate, hGeneric]
        exact smtx_typeof_apply_of_head_cases hHead hX hA
      have hArgWF :
          smtx_type_field_wf_rec A native_reflist_nil :=
        eo_to_smt_quantifiers_skolemize_top_fun_like_arg_field_wf y z hHead
      have hEo :
          __eo_to_smt_type
              (__eo_typeof (Term.Apply (Term._at_quantifiers_skolemize y z) x)) =
            B :=
        eo_to_smt_type_typeof_apply_from_ih_of_fun_like
          (Term._at_quantifiers_skolemize y z) x A B ihF ihX
          hHead hX rfl hArgWF hA
      exact hSmt.trans hEo.symm
  case UOp3 op y z w =>
    cases op
    case _at_re_unfold_pos_component =>
      exfalso
      apply hNonNone
      exact typeof_apply_re_unfold_top_eq_none y z w x
    case _at_witness_string_length =>
      let head := Term.UOp3 UserOp3._at_witness_string_length y z w
      exact eo_to_smt_typeof_matches_translation_apply_generic_from_ih_of_valid
        head x ihFAll ihXAll
        (generic_apply_type_of_non_special_head _ _
          (by
            intro s d i j h
            change native_ite (__eo_to_smt_nat_is_valid z)
                (native_ite (__eo_to_smt_nat_is_valid w)
                  (SmtTerm.choice (native_string_lit "@x") (__eo_to_smt_type y)
                    (SmtTerm.eq
                      (SmtTerm.str_len (SmtTerm.Var (native_string_lit "@x") (__eo_to_smt_type y)))
                      (__eo_to_smt z))) SmtTerm.None) SmtTerm.None =
              SmtTerm.DtSel s d i j at h
            unfold native_ite at h
            split at h <;> try cases h
            split at h <;> cases h)
          (by
            intro s d i h
            change native_ite (__eo_to_smt_nat_is_valid z)
                (native_ite (__eo_to_smt_nat_is_valid w)
                  (SmtTerm.choice (native_string_lit "@x") (__eo_to_smt_type y)
                    (SmtTerm.eq
                      (SmtTerm.str_len (SmtTerm.Var (native_string_lit "@x") (__eo_to_smt_type y)))
                      (__eo_to_smt z))) SmtTerm.None) SmtTerm.None =
              SmtTerm.DtTester s d i at h
            unfold native_ite at h
            split at h <;> try cases h
            split at h <;> cases h))
        (by rfl)
        (by rfl)
        hNonNone
  case UOp op =>
    cases op
    case distinct =>
      exact False.elim (hNotDistinct rfl)
    case _at_purify =>
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        intro hNone
        apply hNonNone
        change __smtx_typeof (SmtTerm._at_purify (__eo_to_smt x)) = SmtType.None
        simpa [__smtx_typeof] using hNone
      exact eo_to_smt_typeof_matches_translation_purify x (ihX hXNonNone)
    case not =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.not) x) =
            SmtTerm.not (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.not (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Bool := by
        have hNotTy : __smtx_typeof (SmtTerm.not (__eo_to_smt x)) = SmtType.Bool := by
          rcases smtx_typeof_not_bool_or_none (__eo_to_smt x) with hBool | hNone
          · exact hBool
          · exfalso
            exact hApplyNN hNone
        rw [typeof_not_eq] at hNotTy
        cases h : __smtx_typeof (__eo_to_smt x) <;>
          simp [native_ite, native_Teq, h] at hNotTy
        rfl
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Bool := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = Term.Bool := eo_to_smt_type_eq_bool hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.not) x)) = SmtType.Bool := by
        rw [hTranslate, typeof_not_eq]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_not_of_bool x hxEo).symm
    case to_real =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.to_real) x) =
            SmtTerm.to_real (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.to_real (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgInt : __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
        to_real_arg_of_non_none (t := __eo_to_smt x) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArgInt]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
        rw [← hXTyped]
        exact hArgInt
      have hxEo : __eo_typeof x = (Term.UOp UserOp.Int) := eo_to_smt_type_eq_int hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.to_real) x)) = SmtType.Real := by
        rw [hTranslate, typeof_to_real_eq]
        simp [hArgInt, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_to_real_of_int x hxEo).symm
    case to_int =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.to_int) x) =
            SmtTerm.to_int (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.to_int (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Real :=
        real_arg_of_non_none (op := SmtTerm.to_int) (t := __eo_to_smt x)
          (typeof_to_int_eq (__eo_to_smt x)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Real := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = (Term.UOp UserOp.Real) := eo_to_smt_type_eq_real hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.to_int) x)) = SmtType.Int := by
        rw [hTranslate, typeof_to_int_eq]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_to_int_of_real x hxEo).symm
    case is_int =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.is_int) x) =
            SmtTerm.is_int (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.is_int (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Real :=
        real_arg_of_non_none (op := SmtTerm.is_int) (t := __eo_to_smt x)
          (typeof_is_int_eq (__eo_to_smt x)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Real := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = (Term.UOp UserOp.Real) := eo_to_smt_type_eq_real hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.is_int) x)) = SmtType.Bool := by
        rw [hTranslate, typeof_is_int_eq]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_is_int_of_real x hxEo).symm
    case abs =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.abs) x) =
            SmtTerm.abs (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.abs (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases abs_arg_of_non_none (t := __eo_to_smt x) hApplyNN with hArgInt | hArgReal
      · have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
          rw [hArgInt]
          simp
        have hXTyped := ihX hXNonNone
        have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
          rw [← hXTyped]
          exact hArgInt
        have hxEo : __eo_typeof x = (Term.UOp UserOp.Int) := eo_to_smt_type_eq_int hxSmt
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.abs) x)) =
              SmtType.Int := by
          rw [hTranslate, typeof_abs_eq]
          simp [__smtx_typeof_arith_overload_op_1, hArgInt]
        exact hSmt.trans (eo_to_smt_type_typeof_apply_abs_of_int x hxEo).symm
      · have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
          rw [hArgReal]
          simp
        have hXTyped := ihX hXNonNone
        have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Real := by
          rw [← hXTyped]
          exact hArgReal
        have hxEo : __eo_typeof x = (Term.UOp UserOp.Real) := eo_to_smt_type_eq_real hxSmt
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.abs) x)) =
              SmtType.Real := by
          rw [hTranslate, typeof_abs_eq]
          simp [__smtx_typeof_arith_overload_op_1, hArgReal]
        have hEo :
            __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.abs) x)) =
              SmtType.Real := by
          change __eo_to_smt_type (__eo_typeof_abs (__eo_typeof x)) = SmtType.Real
          rw [hxEo]
          simp [__eo_typeof_abs, __eo_requires, __is_arith_type,
            native_ite, native_teq, native_not]
        exact hSmt.trans hEo.symm
    case __eoo_neg_2 =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x) =
            SmtTerm.uneg (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.uneg (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg :
          __smtx_typeof (__eo_to_smt x) = SmtType.Int ∨
            __smtx_typeof (__eo_to_smt x) = SmtType.Real := by
        unfold term_has_non_none_type at hApplyNN
        rw [typeof_uneg_eq] at hApplyNN
        cases hTy : __smtx_typeof (__eo_to_smt x) <;>
          simp [__smtx_typeof_arith_overload_op_1, hTy] at hApplyNN
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases hArg with hArgInt | hArgReal
      · have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
          rw [hArgInt]
          simp
        have hXTyped := ihX hXNonNone
        have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
          rw [← hXTyped]
          exact hArgInt
        have hxEo : __eo_typeof x = (Term.UOp UserOp.Int) := eo_to_smt_type_eq_int hxSmt
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x)) =
              SmtType.Int := by
          rw [hTranslate, typeof_uneg_eq]
          simp [__smtx_typeof_arith_overload_op_1, hArgInt]
        have hEo :
            __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x)) =
              SmtType.Int := by
          change __eo_to_smt_type (__eo_typeof_abs (__eo_typeof x)) = SmtType.Int
          rw [hxEo]
          simp [__eo_typeof_abs, __eo_requires, __is_arith_type,
            native_ite, native_teq, native_not]
        exact hSmt.trans hEo.symm
      · have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
          rw [hArgReal]
          simp
        have hXTyped := ihX hXNonNone
        have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Real := by
          rw [← hXTyped]
          exact hArgReal
        have hxEo : __eo_typeof x = (Term.UOp UserOp.Real) := eo_to_smt_type_eq_real hxSmt
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x)) =
              SmtType.Real := by
          rw [hTranslate, typeof_uneg_eq]
          simp [__smtx_typeof_arith_overload_op_1, hArgReal]
        have hEo :
            __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x)) =
              SmtType.Real := by
          change __eo_to_smt_type (__eo_typeof_abs (__eo_typeof x)) = SmtType.Real
          rw [hxEo]
          simp [__eo_typeof_abs, __eo_requires, __is_arith_type,
            native_ite, native_teq, native_not]
        exact hSmt.trans hEo.symm
    case int_pow2 =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.int_pow2) x) =
            SmtTerm.int_pow2 (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.int_pow2 (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
        int_ret_arg_of_non_none (op := SmtTerm.int_pow2)
          (typeof_int_pow2_eq (__eo_to_smt x)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = (Term.UOp UserOp.Int) := eo_to_smt_type_eq_int hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.int_pow2) x)) = SmtType.Int := by
        rw [hTranslate, typeof_int_pow2_eq]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_int_pow2_of_int x hxEo).symm
    case int_log2 =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.int_log2) x) =
            SmtTerm.int_log2 (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.int_log2 (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
        int_ret_arg_of_non_none (op := SmtTerm.int_log2)
          (typeof_int_log2_eq (__eo_to_smt x)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = (Term.UOp UserOp.Int) := eo_to_smt_type_eq_int hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.int_log2) x)) = SmtType.Int := by
        rw [hTranslate, typeof_int_log2_eq]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_int_log2_of_int x hxEo).symm
    case int_ispow2 =>
      let geqTerm :=
        SmtTerm.geq (__eo_to_smt x) (SmtTerm.Numeral 0)
      let eqTerm :=
        SmtTerm.eq (__eo_to_smt x)
          (SmtTerm.int_pow2 (SmtTerm.int_log2 (__eo_to_smt x)))
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.int_ispow2) x) =
            SmtTerm.and geqTerm eqTerm := by
        rfl
      have hApplyNN :
          term_has_non_none_type (SmtTerm.and geqTerm eqTerm) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs :
          __smtx_typeof geqTerm = SmtType.Bool ∧
            __smtx_typeof eqTerm = SmtType.Bool :=
        bool_binop_args_bool_of_non_none (op := SmtTerm.and)
          (typeof_and_eq geqTerm eqTerm) hApplyNN
      have hGeqNN : term_has_non_none_type geqTerm := by
        unfold term_has_non_none_type
        rw [hArgs.1]
        simp
      have hGeqArgs :
          (__smtx_typeof (__eo_to_smt x) = SmtType.Int ∧
              __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int) ∨
            (__smtx_typeof (__eo_to_smt x) = SmtType.Real ∧
              __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Real) :=
        arith_binop_ret_bool_args_of_non_none (op := SmtTerm.geq)
          (typeof_geq_eq (__eo_to_smt x) (SmtTerm.Numeral 0)) hGeqNN

      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Int := by
        rcases hGeqArgs with hInt | hReal
        · exact hInt.1
        · have hZeroReal := hReal.2
          rw [__smtx_typeof.eq_2] at hZeroReal
          simp at hZeroReal
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = (Term.UOp UserOp.Int) := eo_to_smt_type_eq_int hxSmt
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.int_ispow2) x)) = SmtType.Bool := by
        rw [hTranslate, typeof_and_eq geqTerm eqTerm]
        simp [hArgs.1, hArgs.2, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_int_ispow2_of_int x hxEo).symm
    case _at_int_div_by_zero =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) x) =
            SmtTerm.div (__eo_to_smt x) (SmtTerm.Numeral 0) := by
        rfl
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.div (__eo_to_smt x) (SmtTerm.Numeral 0)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs : __smtx_typeof (__eo_to_smt x) = SmtType.Int ∧
          __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int :=
        int_binop_args_of_non_none (op := SmtTerm.div) (R := SmtType.Int)
          (typeof_div_eq (__eo_to_smt x) (SmtTerm.Numeral 0)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArgs.1]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
        rw [← hXTyped]
        exact hArgs.1
      have hxEo : __eo_typeof x = (Term.UOp UserOp.Int) := eo_to_smt_type_eq_int hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) x)) = SmtType.Int := by
        rw [hTranslate, typeof_div_eq (__eo_to_smt x) (SmtTerm.Numeral 0)]
        simp [hArgs.1, hArgs.2, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_at_int_div_by_zero_of_int x hxEo).symm
    case _at_mod_by_zero =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp._at_mod_by_zero) x) =
            SmtTerm.mod (__eo_to_smt x) (SmtTerm.Numeral 0) := by
        rfl
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.mod (__eo_to_smt x) (SmtTerm.Numeral 0)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs : __smtx_typeof (__eo_to_smt x) = SmtType.Int ∧
          __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int :=
        int_binop_args_of_non_none (op := SmtTerm.mod) (R := SmtType.Int)
          (typeof_mod_eq (__eo_to_smt x) (SmtTerm.Numeral 0)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArgs.1]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
        rw [← hXTyped]
        exact hArgs.1
      have hxEo : __eo_typeof x = (Term.UOp UserOp.Int) := eo_to_smt_type_eq_int hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_mod_by_zero) x)) = SmtType.Int := by
        rw [hTranslate, typeof_mod_eq (__eo_to_smt x) (SmtTerm.Numeral 0)]
        simp [hArgs.1, hArgs.2, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_at_mod_by_zero_of_int x hxEo).symm
    case _at_bvsize =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x) =
            let _v0 := __eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))
            native_ite (native_zleq 0 _v0)
              (SmtTerm._at_purify (SmtTerm.Numeral _v0))
              SmtTerm.None := by
        rfl
      have hApplyNN :
          term_has_non_none_type
            (let _v0 := __eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))
             native_ite (native_zleq 0 _v0)
               (SmtTerm._at_purify (SmtTerm.Numeral _v0))
               SmtTerm.None) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgExists : ∃ w : native_Nat, __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w := by
        apply smtx_bv_sizeof_term_non_none (t := __eo_to_smt x)
        unfold term_has_non_none_type at hApplyNN
        exact hApplyNN
      rcases hArgExists with ⟨w, hArg⟩
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w)) :=
        eo_to_smt_type_eq_bitvec hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)) = SmtType.Int := by
        have hWNonneg : native_zleq 0 (native_nat_to_int w) = true := by
          simp [native_zleq, SmtEval.native_zleq, native_nat_to_int, Smtm.native_nat_to_int]
        rw [hTranslate, hArg]
        simp [__eo_to_smt_bv_size, __smtx_typeof, native_ite, hWNonneg]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_at_bvsize_of_bitvec x w hxEo).symm
    case bvnot =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.bvnot) x) =
            SmtTerm.bvnot (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.bvnot (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases bv_unop_arg_of_non_none (op := SmtTerm.bvnot)
          (typeof_bvnot_eq (__eo_to_smt x)) hApplyNN with ⟨w, hArg⟩
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w)) :=
        eo_to_smt_type_eq_bitvec hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvnot) x)) = SmtType.BitVec w := by
        rw [hTranslate, typeof_bvnot_eq (__eo_to_smt x), hArg]
        simp [__smtx_typeof_bv_op_1]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_bvnot_of_bitvec x w hxEo).symm
    case bvneg =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.bvneg) x) =
            SmtTerm.bvneg (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.bvneg (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases bv_unop_arg_of_non_none (op := SmtTerm.bvneg)
          (typeof_bvneg_eq (__eo_to_smt x)) hApplyNN with ⟨w, hArg⟩
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w)) :=
        eo_to_smt_type_eq_bitvec hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvneg) x)) = SmtType.BitVec w := by
        rw [hTranslate, typeof_bvneg_eq (__eo_to_smt x), hArg]
        simp [__smtx_typeof_bv_op_1]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_bvneg_of_bitvec x w hxEo).symm
    case bvnego =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.bvnego) x) =
            SmtTerm.bvnego (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.bvnego (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases bv_unop_ret_arg_of_non_none (op := SmtTerm.bvnego) (ret := SmtType.Bool)
          (typeof_bvnego_eq (__eo_to_smt x)) hApplyNN with
        ⟨w, hArg⟩
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w)) :=
        eo_to_smt_type_eq_bitvec hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvnego) x)) = SmtType.Bool := by
        rw [hTranslate, typeof_bvnego_eq (__eo_to_smt x), hArg]
        simp [__smtx_typeof_bv_op_1_ret]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_bvnego_of_bitvec x w hxEo).symm
    case bvredand =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.bvredand) x) =
            let _v0 := __eo_to_smt x
            SmtTerm.bvcomp _v0
              (SmtTerm.bvnot
                (SmtTerm.Binary (__eo_to_smt_bv_size (__smtx_typeof _v0)) 0)) := by
        rfl
      have hApplyNN :
          term_has_non_none_type
            (let _v0 := __eo_to_smt x
             SmtTerm.bvcomp _v0
               (SmtTerm.bvnot
                 (SmtTerm.Binary (__eo_to_smt_bv_size (__smtx_typeof _v0)) 0))) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases bv_binop_ret_args_of_non_none
          (op := SmtTerm.bvcomp) (ret := SmtType.BitVec 1)
          (typeof_bvcomp_eq
            (__eo_to_smt x)
            (SmtTerm.bvnot (SmtTerm.Binary (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))) 0)))
          hApplyNN with
        ⟨w, hArgX, hArgY⟩
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArgX]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w := by
        rw [← hXTyped]
        exact hArgX
      have hxEo : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w)) :=
        eo_to_smt_type_eq_bitvec hxSmt
      have hArgY' :
          __smtx_typeof
              (SmtTerm.bvnot
                (SmtTerm.Binary (__eo_to_smt_bv_size (SmtType.BitVec w)) 0)) =
            SmtType.BitVec w := by
        simpa [hArgX] using hArgY
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvredand) x)) = SmtType.BitVec 1 := by
        rw [hTranslate]
        rw [typeof_bvcomp_eq]
        rw [hArgX, hArgY']
        simp [__smtx_typeof_bv_op_2_ret, native_ite, native_nateq, Smtm.native_nateq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_bvredand_of_bitvec x w hxEo).symm
    case bvredor =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.bvredor) x) =
            let _v0 := __eo_to_smt x
            SmtTerm.bvnot
              (SmtTerm.bvcomp _v0
                (SmtTerm.Binary (__eo_to_smt_bv_size (__smtx_typeof _v0)) 0)) := by
        rfl
      have hApplyNN :
          term_has_non_none_type
            (let _v0 := __eo_to_smt x
             SmtTerm.bvnot
               (SmtTerm.bvcomp _v0
                 (SmtTerm.Binary (__eo_to_smt_bv_size (__smtx_typeof _v0)) 0))) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hInner :
          ∃ w : native_Nat,
            __smtx_typeof
                (SmtTerm.bvcomp
                  (__eo_to_smt x)
                  (SmtTerm.Binary (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))) 0)) =
              SmtType.BitVec w := by
        rcases bv_unop_arg_of_non_none (op := SmtTerm.bvnot)
            (typeof_bvnot_eq
              (SmtTerm.bvcomp
                (__eo_to_smt x)
                (SmtTerm.Binary (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))) 0)))
            hApplyNN with ⟨w, hInner⟩
        exact ⟨w, hInner⟩
      rcases hInner with ⟨_, hInnerTy⟩
      have hInnerNN :
          term_has_non_none_type
            (SmtTerm.bvcomp
              (__eo_to_smt x)
              (SmtTerm.Binary (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))) 0)) := by
        unfold term_has_non_none_type
        rw [hInnerTy]
        simp
      rcases bv_binop_ret_args_of_non_none
          (op := SmtTerm.bvcomp) (ret := SmtType.BitVec 1)
          (typeof_bvcomp_eq
            (__eo_to_smt x)
            (SmtTerm.Binary (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))) 0))
          hInnerNN with
        ⟨w, hArgX, hArgY⟩
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArgX]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w := by
        rw [← hXTyped]
        exact hArgX
      have hxEo : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w)) :=
        eo_to_smt_type_eq_bitvec hxSmt
      have hArgY' :
          __smtx_typeof (SmtTerm.Binary (__eo_to_smt_bv_size (SmtType.BitVec w)) 0) =
            SmtType.BitVec w := by
        simpa [hArgX] using hArgY
      have hInnerOne :
          __smtx_typeof
              (SmtTerm.bvcomp
                (__eo_to_smt x)
                (SmtTerm.Binary (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))) 0)) =
            SmtType.BitVec 1 := by
        rw [typeof_bvcomp_eq]
        rw [hArgX, hArgY']
        simp [__smtx_typeof_bv_op_2_ret, native_ite, native_nateq, Smtm.native_nateq]
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvredor) x)) = SmtType.BitVec 1 := by
        rw [hTranslate, typeof_bvnot_eq]
        rw [hInnerOne]
        simp [__smtx_typeof_bv_op_1]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_bvredor_of_bitvec x w hxEo).symm
    case str_len =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) x) =
            SmtTerm.str_len (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.str_len (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgExists : ∃ T, __smtx_typeof (__eo_to_smt x) = SmtType.Seq T := by
        exact seq_arg_of_non_none_ret (op := SmtTerm.str_len)
          (typeof_str_len_eq (__eo_to_smt x)) hApplyNN
      rcases hArgExists with ⟨T, hArg⟩
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
        rw [← hXTyped]
        exact hArg
      rcases eo_to_smt_type_eq_seq hxSmt with ⟨V, hxEo, hV⟩
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) x)) = SmtType.Int := by
        rw [hTranslate, typeof_str_len_eq (__eo_to_smt x), hArg]
        simp [__smtx_typeof_seq_op_1_ret]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_str_len_of_seq x V hxEo).symm
    case str_rev =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) x) =
            SmtTerm.str_rev (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.str_rev (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases seq_arg_of_non_none (op := SmtTerm.str_rev)
          (typeof_str_rev_eq (__eo_to_smt x)) hApplyNN with ⟨T, hArg⟩
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
        rw [← hXTyped]
        exact hArg
      rcases eo_to_smt_type_eq_seq hxSmt with ⟨V, hxEo, hV⟩
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) x)) = SmtType.Seq T := by
        rw [hTranslate, typeof_str_rev_eq (__eo_to_smt x)]
        simp [__smtx_typeof_seq_op_1, hArg]
      have hEo :
          __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.str_rev) x)) =
            SmtType.Seq (__eo_to_smt_type V) :=
        eo_to_smt_type_typeof_apply_str_rev_of_seq x V hxEo (by
          intro hNone
          rw [hxEo] at hxSmt
          simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hNone] at hxSmt)
      rw [hV] at hEo
      exact hSmt.trans hEo.symm
    case str_to_lower =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_lower) x) =
            SmtTerm.str_to_lower (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.str_to_lower (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
        seq_char_arg_of_non_none (op := SmtTerm.str_to_lower)
          (typeof_str_to_lower_eq (__eo_to_smt x)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq SmtType.Char := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := eo_to_smt_type_eq_seq_char hxSmt
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_lower) x)) =
            SmtType.Seq SmtType.Char := by
        rw [hTranslate, typeof_str_to_lower_eq (__eo_to_smt x)]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_str_to_lower_of_seq_char x hxEo).symm
    case str_to_upper =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_upper) x) =
            SmtTerm.str_to_upper (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.str_to_upper (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
        seq_char_arg_of_non_none (op := SmtTerm.str_to_upper)
          (typeof_str_to_upper_eq (__eo_to_smt x)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq SmtType.Char := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := eo_to_smt_type_eq_seq_char hxSmt
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_upper) x)) =
            SmtType.Seq SmtType.Char := by
        rw [hTranslate, typeof_str_to_upper_eq (__eo_to_smt x)]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_str_to_upper_of_seq_char x hxEo).symm
    case str_to_code =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_code) x) =
            SmtTerm.str_to_code (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.str_to_code (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
        seq_char_arg_of_non_none (op := SmtTerm.str_to_code)
          (typeof_str_to_code_eq (__eo_to_smt x)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq SmtType.Char := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := eo_to_smt_type_eq_seq_char hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_code) x)) = SmtType.Int := by
        rw [hTranslate, typeof_str_to_code_eq (__eo_to_smt x)]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_str_to_code_of_seq_char x hxEo).symm
    case str_from_code =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.str_from_code) x) =
            SmtTerm.str_from_code (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.str_from_code (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
        int_ret_arg_of_non_none (op := SmtTerm.str_from_code) (R := SmtType.Seq SmtType.Char)
          (typeof_str_from_code_eq (__eo_to_smt x)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = (Term.UOp UserOp.Int) := eo_to_smt_type_eq_int hxSmt
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_from_code) x)) =
            SmtType.Seq SmtType.Char := by
        rw [hTranslate, typeof_str_from_code_eq (__eo_to_smt x)]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_str_from_code_of_int x hxEo).symm
    case str_is_digit =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.str_is_digit) x) =
            SmtTerm.str_is_digit (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.str_is_digit (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
        seq_char_arg_of_non_none (op := SmtTerm.str_is_digit)
          (typeof_str_is_digit_eq (__eo_to_smt x)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq SmtType.Char := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := eo_to_smt_type_eq_seq_char hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_is_digit) x)) = SmtType.Bool := by
        rw [hTranslate, typeof_str_is_digit_eq (__eo_to_smt x)]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_str_is_digit_of_seq_char x hxEo).symm
    case str_to_int =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_int) x) =
            SmtTerm.str_to_int (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.str_to_int (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
        seq_char_arg_of_non_none (op := SmtTerm.str_to_int)
          (typeof_str_to_int_eq (__eo_to_smt x)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq SmtType.Char := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := eo_to_smt_type_eq_seq_char hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_int) x)) = SmtType.Int := by
        rw [hTranslate, typeof_str_to_int_eq (__eo_to_smt x)]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_str_to_int_of_seq_char x hxEo).symm
    case _at_strings_stoi_non_digit =>
      let digits :=
        SmtTerm.re_range (SmtTerm.String (native_string_lit "0"))
          (SmtTerm.String (native_string_lit "9"))
      let nonDigit := SmtTerm.re_inter SmtTerm.re_allchar (SmtTerm.re_comp digits)
      have hTranslate :
          __eo_to_smt (Term._at_strings_stoi_non_digit x) =
            SmtTerm.str_indexof_re (__eo_to_smt x) nonDigit (SmtTerm.Numeral 0) := by
        rfl
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.str_indexof_re (__eo_to_smt x) nonDigit (SmtTerm.Numeral 0)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := str_indexof_re_args_of_non_none hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArgs.1]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq SmtType.Char := by
        rw [← hXTyped]
        exact hArgs.1
      have hxEo : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) :=
        eo_to_smt_type_eq_seq_char hxSmt
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term._at_strings_stoi_non_digit x)) =
            SmtType.Int := by
        rw [hTranslate]
        exact smtx_typeof_str_indexof_re_of_non_none
          (__eo_to_smt x) nonDigit (SmtTerm.Numeral 0) hApplyNN
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_at_strings_stoi_non_digit_of_seq_char x hxEo).symm
    case str_from_int =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.str_from_int) x) =
            SmtTerm.str_from_int (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.str_from_int (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
        int_ret_arg_of_non_none (op := SmtTerm.str_from_int) (R := SmtType.Seq SmtType.Char)
          (typeof_str_from_int_eq (__eo_to_smt x)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = (Term.UOp UserOp.Int) := eo_to_smt_type_eq_int hxSmt
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_from_int) x)) =
            SmtType.Seq SmtType.Char := by
        rw [hTranslate, typeof_str_from_int_eq (__eo_to_smt x)]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_str_from_int_of_int x hxEo).symm
    case str_to_re =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_re) x) =
            SmtTerm.str_to_re (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.str_to_re (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
        seq_char_arg_of_non_none (op := SmtTerm.str_to_re)
          (typeof_str_to_re_eq (__eo_to_smt x)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq SmtType.Char := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := eo_to_smt_type_eq_seq_char hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_re) x)) = SmtType.RegLan := by
        rw [hTranslate, typeof_str_to_re_eq (__eo_to_smt x)]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_str_to_re_of_seq_char x hxEo).symm
    case re_mult =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) x) =
            SmtTerm.re_mult (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.re_mult (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan :=
        reglan_arg_of_non_none (op := SmtTerm.re_mult)
          (typeof_re_mult_eq (__eo_to_smt x)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.RegLan := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = (Term.UOp UserOp.RegLan) := eo_to_smt_type_eq_reglan hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) x)) = SmtType.RegLan := by
        rw [hTranslate, typeof_re_mult_eq (__eo_to_smt x)]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_re_mult_of_reglan x hxEo).symm
    case re_plus =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.re_plus) x) =
            SmtTerm.re_plus (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.re_plus (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan :=
        reglan_arg_of_non_none (op := SmtTerm.re_plus)
          (typeof_re_plus_eq (__eo_to_smt x)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.RegLan := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = (Term.UOp UserOp.RegLan) := eo_to_smt_type_eq_reglan hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_plus) x)) = SmtType.RegLan := by
        rw [hTranslate, typeof_re_plus_eq (__eo_to_smt x)]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_re_plus_of_reglan x hxEo).symm
    case re_opt =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.re_opt) x) =
            SmtTerm.re_opt (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.re_opt (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan :=
        reglan_arg_of_non_none (op := SmtTerm.re_opt)
          (typeof_re_opt_eq (__eo_to_smt x)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.RegLan := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = (Term.UOp UserOp.RegLan) := eo_to_smt_type_eq_reglan hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_opt) x)) = SmtType.RegLan := by
        rw [hTranslate, typeof_re_opt_eq (__eo_to_smt x)]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_re_opt_of_reglan x hxEo).symm
    case re_comp =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.re_comp) x) =
            SmtTerm.re_comp (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.re_comp (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan :=
        reglan_arg_of_non_none (op := SmtTerm.re_comp)
          (typeof_re_comp_eq (__eo_to_smt x)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.RegLan := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = (Term.UOp UserOp.RegLan) := eo_to_smt_type_eq_reglan hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_comp) x)) = SmtType.RegLan := by
        rw [hTranslate, typeof_re_comp_eq (__eo_to_smt x)]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_re_comp_of_reglan x hxEo).symm
    case seq_unit =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) x) =
            SmtTerm.seq_unit (__eo_to_smt x) := by
        rfl
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        intro hXNone
        apply hNonNone
        rw [hTranslate, typeof_seq_unit_eq (__eo_to_smt x), hXNone]
        simp [__smtx_typeof_guard_wf, __smtx_type_wf, __smtx_type_wf_rec,
          native_and, native_ite]
      have hXTyped := ihX hXNonNone
      have hxEoNonNone : __eo_to_smt_type (__eo_typeof x) ≠ SmtType.None := by
        rw [← hXTyped]
        exact hXNonNone
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) x)) =
            SmtType.Seq (__eo_to_smt_type (__eo_typeof x)) := by
        have hGuardNN :
            __smtx_typeof_guard_wf
                (SmtType.Seq (__smtx_typeof (__eo_to_smt x)))
                (SmtType.Seq (__smtx_typeof (__eo_to_smt x))) ≠
              SmtType.None := by
          rw [hTranslate, typeof_seq_unit_eq (__eo_to_smt x)] at hNonNone
          exact hNonNone
        have hGuard :
            __smtx_typeof_guard_wf
                (SmtType.Seq (__eo_to_smt_type (__eo_typeof x)))
                (SmtType.Seq (__eo_to_smt_type (__eo_typeof x))) =
              SmtType.Seq (__eo_to_smt_type (__eo_typeof x)) := by
          rw [← hXTyped]
          exact smtx_typeof_guard_wf_of_non_none
            (SmtType.Seq (__smtx_typeof (__eo_to_smt x)))
            (SmtType.Seq (__smtx_typeof (__eo_to_smt x))) hGuardNN
        rw [hTranslate, typeof_seq_unit_eq (__eo_to_smt x), hXTyped]
        exact hGuard
      exact hSmt.trans (eo_to_smt_type_typeof_apply_seq_unit_of_non_none x hxEoNonNone).symm
    case set_singleton =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.set_singleton) x) =
            SmtTerm.set_singleton (__eo_to_smt x) := by
        rfl
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        intro hXNone
        apply hNonNone
        rw [hTranslate, typeof_set_singleton_eq (__eo_to_smt x), hXNone]
        simp [__smtx_typeof_guard_wf, __smtx_type_wf, __smtx_type_wf_rec,
          native_and, native_ite]
      have hXTyped := ihX hXNonNone
      have hxEoNonNone : __eo_to_smt_type (__eo_typeof x) ≠ SmtType.None := by
        rw [← hXTyped]
        exact hXNonNone
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_singleton) x)) =
            SmtType.Set (__eo_to_smt_type (__eo_typeof x)) := by
        have hGuardNN :
            __smtx_typeof_guard_wf
                (SmtType.Set (__smtx_typeof (__eo_to_smt x)))
                (SmtType.Set (__smtx_typeof (__eo_to_smt x))) ≠
              SmtType.None := by
          rw [hTranslate, typeof_set_singleton_eq (__eo_to_smt x)] at hNonNone
          exact hNonNone
        have hGuard :
            __smtx_typeof_guard_wf
                (SmtType.Set (__eo_to_smt_type (__eo_typeof x)))
                (SmtType.Set (__eo_to_smt_type (__eo_typeof x))) =
              SmtType.Set (__eo_to_smt_type (__eo_typeof x)) := by
          rw [← hXTyped]
          exact smtx_typeof_guard_wf_of_non_none
            (SmtType.Set (__smtx_typeof (__eo_to_smt x)))
            (SmtType.Set (__smtx_typeof (__eo_to_smt x))) hGuardNN
        rw [hTranslate, typeof_set_singleton_eq (__eo_to_smt x), hXTyped]
        exact hGuard
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_set_singleton_of_non_none x hxEoNonNone).symm
    case set_choose =>
      exact eo_to_smt_typeof_matches_translation_apply_set_choose x ihX hNonNone
    case set_is_empty =>
      let T := __eo_to_smt_set_elem_type (__smtx_typeof (__eo_to_smt x))
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.set_is_empty) x) =
            SmtTerm.eq (__eo_to_smt x) (SmtTerm.set_empty T) := by
        rfl
      have hEqNN :
          __smtx_typeof_eq
              (__smtx_typeof (__eo_to_smt x))
              (__smtx_typeof (SmtTerm.set_empty T)) ≠
            SmtType.None := by
        simpa [hTranslate, typeof_eq_eq] using hNonNone
      have hEqArgs := smtx_typeof_eq_non_none hEqNN
      have hEmptyNN :
          __smtx_typeof (SmtTerm.set_empty T) ≠ SmtType.None := by
        rw [← hEqArgs.1]
        exact hEqArgs.2
      have hEmptyGuard :
          __smtx_typeof_guard_wf (SmtType.Set T) (SmtType.Set T) =
            SmtType.Set T := by
        exact smtx_typeof_guard_wf_of_non_none
          (SmtType.Set T) (SmtType.Set T) (by
            simpa [typeof_set_empty_eq] using hEmptyNN)
      have hXTy :
          __smtx_typeof (__eo_to_smt x) = SmtType.Set T := by
        rw [hEqArgs.1, typeof_set_empty_eq]
        exact hEmptyGuard
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hXTy]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt :
          __eo_to_smt_type (__eo_typeof x) = SmtType.Set T := by
        rw [← hXTyped]
        exact hXTy
      rcases TranslationProofs.eo_to_smt_type_eq_set hxSmt with ⟨U, hxEo, _hU⟩
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_is_empty) x)) =
            SmtType.Bool := by
        rw [hTranslate, typeof_eq_eq]
        simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq,
          hEqArgs.1, hEmptyNN]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_set_is_empty_of_set x U hxEo).symm
    case set_is_singleton =>
      let T := __eo_to_smt_set_elem_type (__smtx_typeof (__eo_to_smt x))
      let diff :=
        SmtTerm.map_diff (__eo_to_smt x) (SmtTerm.set_empty T)
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.set_is_singleton) x) =
            SmtTerm.eq (__eo_to_smt x)
              (SmtTerm.set_singleton diff) := by
        rfl
      have hEqNN :
          __smtx_typeof_eq
              (__smtx_typeof (__eo_to_smt x))
              (__smtx_typeof (SmtTerm.set_singleton diff)) ≠
            SmtType.None := by
        simpa [hTranslate, typeof_eq_eq] using hNonNone
      have hEqArgs := smtx_typeof_eq_non_none hEqNN
      have hSingletonNN :
          __smtx_typeof (SmtTerm.set_singleton diff) ≠ SmtType.None := by
        rw [← hEqArgs.1]
        exact hEqArgs.2
      have hSingletonGuard :
          __smtx_typeof_guard_wf
              (SmtType.Set (__smtx_typeof diff))
              (SmtType.Set (__smtx_typeof diff)) =
            SmtType.Set (__smtx_typeof diff) := by
        exact smtx_typeof_guard_wf_of_non_none
          (SmtType.Set (__smtx_typeof diff))
          (SmtType.Set (__smtx_typeof diff)) (by
            simpa [typeof_set_singleton_eq] using hSingletonNN)
      have hXTy :
          __smtx_typeof (__eo_to_smt x) =
            SmtType.Set (__smtx_typeof diff) := by
        rw [hEqArgs.1, typeof_set_singleton_eq]
        exact hSingletonGuard
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hXTy]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt :
          __eo_to_smt_type (__eo_typeof x) =
            SmtType.Set (__smtx_typeof diff) := by
        rw [← hXTyped]
        exact hXTy
      rcases TranslationProofs.eo_to_smt_type_eq_set hxSmt with ⟨U, hxEo, _hU⟩
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_is_singleton) x)) =
            SmtType.Bool := by
        rw [hTranslate, typeof_eq_eq]
        simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq,
          hEqArgs.1, hSingletonNN]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_set_is_singleton_of_set x U hxEo).symm
    case _at_div_by_zero =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp._at_div_by_zero) x) =
            SmtTerm.qdiv (__eo_to_smt x) (SmtTerm.Rational (native_mk_rational 0 1)) := by
        rfl
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.qdiv (__eo_to_smt x) (SmtTerm.Rational (native_mk_rational 0 1))) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs :
          (__smtx_typeof (__eo_to_smt x) = SmtType.Int ∧
              __smtx_typeof (SmtTerm.Rational (native_mk_rational 0 1)) = SmtType.Int) ∨
            (__smtx_typeof (__eo_to_smt x) = SmtType.Real ∧
              __smtx_typeof (SmtTerm.Rational (native_mk_rational 0 1)) = SmtType.Real) :=
        arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv) (R := SmtType.Real)
          (typeof_qdiv_eq (__eo_to_smt x) (SmtTerm.Rational (native_mk_rational 0 1))) hApplyNN
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Real := by
        rcases hArgs with hInt | hReal
        · have hZeroInt := hInt.2
          rw [typeof_rational_eq] at hZeroInt
          cases hZeroInt
        · exact hReal.1
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Real := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = (Term.UOp UserOp.Real) := eo_to_smt_type_eq_real hxSmt
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_div_by_zero) x)) = SmtType.Real := by
        rw [hTranslate, typeof_qdiv_eq (__eo_to_smt x) (SmtTerm.Rational (native_mk_rational 0 1)),
          typeof_rational_eq, hArg]
        simp [__smtx_typeof_arith_overload_op_2_ret]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_at_div_by_zero_of_real x hxEo).symm
    case ubv_to_int =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.ubv_to_int) x) =
            SmtTerm.ubv_to_int (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.ubv_to_int (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases bv_unop_ret_arg_of_non_none (op := SmtTerm.ubv_to_int) (ret := SmtType.Int)
          (by rw [__smtx_typeof.eq_def] <;> simp only) hApplyNN with
        ⟨w, hArg⟩
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w)) :=
        eo_to_smt_type_eq_bitvec hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.ubv_to_int) x)) = SmtType.Int := by
        rw [hTranslate]
        rw [__smtx_typeof.eq_def] <;> simp only
        rw [hArg]
        simp [__smtx_typeof_bv_op_1_ret]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_ubv_to_int_of_bitvec x w hxEo).symm
    case sbv_to_int =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.sbv_to_int) x) =
            SmtTerm.sbv_to_int (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.sbv_to_int (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases bv_unop_ret_arg_of_non_none (op := SmtTerm.sbv_to_int) (ret := SmtType.Int)
          (by rw [__smtx_typeof.eq_def] <;> simp only) hApplyNN with
        ⟨w, hArg⟩
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w)) :=
        eo_to_smt_type_eq_bitvec hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.sbv_to_int) x)) = SmtType.Int := by
        rw [hTranslate]
        rw [__smtx_typeof.eq_def] <;> simp only
        rw [hArg]
        simp [__smtx_typeof_bv_op_1_ret]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_sbv_to_int_of_bitvec x w hxEo).symm
    all_goals
      refine eo_to_smt_typeof_matches_translation_apply_uop_remaining_obligation _ x ?_ hNonNone
      first
      | change __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) = SmtType.None
        exact typeof_apply_none_eq (__eo_to_smt x)
      | change __smtx_typeof (SmtTerm.Apply SmtTerm.re_allchar (__eo_to_smt x)) = SmtType.None
        exact typeof_apply_reglan_head_eq_none _ _
          (by unfold __smtx_typeof; rfl)
          (by intro s d i j h; cases h)
          (by intro s d i h; cases h)
      | change __smtx_typeof (SmtTerm.Apply SmtTerm.re_none (__eo_to_smt x)) = SmtType.None
        exact typeof_apply_reglan_head_eq_none _ _
          (by unfold __smtx_typeof; rfl)
          (by intro s d i j h; cases h)
          (by intro s d i h; cases h)
      | change __smtx_typeof (SmtTerm.Apply SmtTerm.re_all (__eo_to_smt x)) = SmtType.None
        exact typeof_apply_reglan_head_eq_none _ _
          (by unfold __smtx_typeof; rfl)
          (by intro s d i j h; cases h)
          (by intro s d i h; cases h)
      | change
          __smtx_typeof
              (SmtTerm.Apply
                (SmtTerm.DtCons (native_string_lit "@Tuple")
                  (__eo_to_smt_tuple_decl
                    (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)) 0)
                (__eo_to_smt x)) =
            SmtType.None
        exact typeof_apply_tuple_unit_eq_none (__eo_to_smt x)
  all_goals
    refine eo_to_smt_typeof_matches_translation_apply_constructor_fallback_obligation
      _ x ?_ hNonNone
    first
    | change __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) = SmtType.None
      exact typeof_apply_none_eq (__eo_to_smt x)
    | change
        __smtx_typeof
            (SmtTerm.Apply (__eo_to_smt_seq_empty (__eo_to_smt_type _)) (__eo_to_smt x)) =
          SmtType.None
      exact typeof_apply_eo_to_smt_seq_empty_eq_none _ (__eo_to_smt x)
    | change __smtx_typeof (SmtTerm.Apply (SmtTerm.Boolean _) (__eo_to_smt x)) = SmtType.None
      exact typeof_apply_boolean_head_eq_none _ (__eo_to_smt x)
    | change __smtx_typeof (SmtTerm.Apply (SmtTerm.Numeral _) (__eo_to_smt x)) = SmtType.None
      exact typeof_apply_numeral_head_eq_none _ (__eo_to_smt x)
    | change __smtx_typeof (SmtTerm.Apply (SmtTerm.Rational _) (__eo_to_smt x)) = SmtType.None
      exact typeof_apply_rational_head_eq_none _ (__eo_to_smt x)
    | change __smtx_typeof (SmtTerm.Apply (SmtTerm.String _) (__eo_to_smt x)) = SmtType.None
      exact typeof_apply_string_head_eq_none _ (__eo_to_smt x)
    | change __smtx_typeof (SmtTerm.Apply (SmtTerm.Binary _ _) (__eo_to_smt x)) = SmtType.None
      exact typeof_apply_binary_head_eq_none _ _ (__eo_to_smt x)

/--
Applying a term with an SMT translation uses the generic Eunoia application
typing rule. In particular, a translated head cannot be one of the partial
applications whose next argument triggers a specialized `__eo_typeof` clause.
-/
theorem eo_typeof_apply_eq_of_non_none_translation
    (f x : Term)
    (hTransF : __smtx_typeof (__eo_to_smt f) ≠ SmtType.None) :
    __eo_typeof (Term.Apply f x) =
      __eo_typeof_apply (__eo_typeof f) (__eo_typeof x) := by
  cases f <;> try rfl
  case __eo_List_cons =>
    exfalso
    apply hTransF
    exact smtx_typeof_none
  case UOp op =>
    cases op <;> try rfl
    all_goals
      exfalso
      apply hTransF
      exact smtx_typeof_none
  case UOp1 op i =>
    cases op <;> try rfl
    all_goals
      exfalso
      apply hTransF
      exact smtx_typeof_none
  case UOp2 op i j =>
    cases op <;> try rfl
    all_goals
      exfalso
      apply hTransF
      exact smtx_typeof_none
  case Apply f a =>
    cases f <;> try rfl
    case UOp op =>
      cases op <;> try rfl
      all_goals
        exfalso
        apply hTransF
        exact typeof_apply_none_eq (__eo_to_smt a)
    case UOp1 op i =>
      cases op <;> try rfl
      all_goals
        exfalso
        apply hTransF
        exact typeof_apply_none_eq (__eo_to_smt a)
    case FunType =>
      exfalso
      apply hTransF
      exact typeof_apply_none_eq (__eo_to_smt a)
    case Apply f' b =>
      cases f' <;> try rfl
      case UOp op =>
        cases op <;> try rfl
        all_goals
          exfalso
          apply hTransF
          exact typeof_apply_apply_none_head_eq
            (__eo_to_smt b) (__eo_to_smt a)
      case Apply f'' c =>
        cases f'' <;> try rfl
        case UOp op =>
          cases op <;> try rfl
          all_goals
            exfalso
            apply hTransF
            exact typeof_apply_apply_apply_none_head_eq
              (__eo_to_smt c) (__eo_to_smt b) (__eo_to_smt a)

end TranslationProofs
