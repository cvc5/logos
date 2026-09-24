module

public import Cpc.Proofs.TypePreservation.Datatypes
import all Cpc.SmtModel
import all Cpc.Proofs.TypePreservation.Common

public section

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

/-- Rewrites the typing equation for `ite`. -/
theorem typeof_ite_eq
    (c t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.ite c t1 t2) =
      __smtx_typeof_ite (__smtx_typeof c) (__smtx_typeof t1) (__smtx_typeof t2) := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Rewrites the typing equation for `select`. -/
theorem typeof_select_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.select t1 t2) =
      __smtx_typeof_select (__smtx_typeof t1) (__smtx_typeof t2) := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Rewrites the typing equation for `store`. -/
theorem typeof_store_eq
    (t1 t2 t3 : SmtTerm) :
    __smtx_typeof (SmtTerm.store t1 t2 t3) =
      __smtx_typeof_store (__smtx_typeof t1) (__smtx_typeof t2) (__smtx_typeof t3) := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Rewrites the typing equation for `map_diff`. -/
theorem typeof_map_diff_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.map_diff t1 t2) =
      __smtx_typeof_map_diff (__smtx_typeof t1) (__smtx_typeof t2) := by
  simp [__smtx_typeof]

/-- Rewrites the typing equation for `eq`. -/
theorem typeof_eq_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.eq t1 t2) =
      __smtx_typeof_eq (__smtx_typeof t1) (__smtx_typeof t2) := by
  rw [__smtx_typeof.eq_def] <;> simp only
theorem typeof_not_eq (t : SmtTerm) :
    __smtx_typeof (SmtTerm.not t) =
      native_ite (native_Teq (__smtx_typeof t) SmtType.Bool) SmtType.Bool SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
theorem typeof_or_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.or t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) SmtType.Bool)
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.Bool) SmtType.Bool SmtType.None)
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
theorem typeof_and_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.and t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) SmtType.Bool)
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.Bool) SmtType.Bool SmtType.None)
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
theorem typeof_imp_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.imp t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) SmtType.Bool)
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.Bool) SmtType.Bool SmtType.None)
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
theorem typeof_xor_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.xor t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) SmtType.Bool)
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.Bool) SmtType.Bool SmtType.None)
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
theorem typeof_plus_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.plus t1 t2) =
      __smtx_typeof_arith_overload_op_2 (__smtx_typeof t1) (__smtx_typeof t2) := by
  rw [__smtx_typeof.eq_def] <;> simp only
theorem typeof_neg_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.neg t1 t2) =
      __smtx_typeof_arith_overload_op_2 (__smtx_typeof t1) (__smtx_typeof t2) := by
  rw [__smtx_typeof.eq_def] <;> simp only
theorem typeof_mult_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.mult t1 t2) =
      __smtx_typeof_arith_overload_op_2 (__smtx_typeof t1) (__smtx_typeof t2) := by
  rw [__smtx_typeof.eq_def] <;> simp only
theorem typeof_lt_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.lt t1 t2) =
      __smtx_typeof_arith_overload_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool := by
  rw [__smtx_typeof.eq_def] <;> simp only
theorem typeof_leq_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.leq t1 t2) =
      __smtx_typeof_arith_overload_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool := by
  rw [__smtx_typeof.eq_def] <;> simp only
theorem typeof_gt_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.gt t1 t2) =
      __smtx_typeof_arith_overload_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool := by
  rw [__smtx_typeof.eq_def] <;> simp only
theorem typeof_geq_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.geq t1 t2) =
      __smtx_typeof_arith_overload_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool := by
  rw [__smtx_typeof.eq_def] <;> simp only
theorem typeof_to_real_eq (t : SmtTerm) :
    __smtx_typeof (SmtTerm.to_real t) =
      native_ite (native_Teq (__smtx_typeof t) SmtType.Int) SmtType.Real SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
theorem typeof_to_int_eq (t : SmtTerm) :
    __smtx_typeof (SmtTerm.to_int t) =
      native_ite (native_Teq (__smtx_typeof t) SmtType.Real) SmtType.Int SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
theorem typeof_is_int_eq (t : SmtTerm) :
    __smtx_typeof (SmtTerm.is_int t) =
      native_ite (native_Teq (__smtx_typeof t) SmtType.Real) SmtType.Bool SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
theorem typeof_abs_eq (t : SmtTerm) :
    __smtx_typeof (SmtTerm.abs t) =
      __smtx_typeof_arith_overload_op_1 (__smtx_typeof t) := by
  rw [__smtx_typeof.eq_def] <;> simp only
theorem typeof_uneg_eq (t : SmtTerm) :
    __smtx_typeof (SmtTerm.uneg t) =
      __smtx_typeof_arith_overload_op_1 (__smtx_typeof t) := by
  rw [__smtx_typeof.eq_def] <;> simp only
theorem typeof_div_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.div t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) SmtType.Int)
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.Int) SmtType.Int SmtType.None)
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
theorem typeof_mod_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.mod t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) SmtType.Int)
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.Int) SmtType.Int SmtType.None)
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
theorem typeof_divisible_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.divisible t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) SmtType.Int)
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.Int) SmtType.Bool SmtType.None)
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
theorem typeof_int_pow2_eq (t : SmtTerm) :
    __smtx_typeof (SmtTerm.int_pow2 t) =
      native_ite (native_Teq (__smtx_typeof t) SmtType.Int) SmtType.Int SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
theorem typeof_int_log2_eq (t : SmtTerm) :
    __smtx_typeof (SmtTerm.int_log2 t) =
      native_ite (native_Teq (__smtx_typeof t) SmtType.Int) SmtType.Int SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
theorem typeof_div_total_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.div_total t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) SmtType.Int)
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.Int) SmtType.Int SmtType.None)
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
theorem typeof_mod_total_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.mod_total t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) SmtType.Int)
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.Int) SmtType.Int SmtType.None)
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
theorem typeof_qdiv_total_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.qdiv_total t1 t2) =
      __smtx_typeof_arith_overload_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Real := by
  rw [__smtx_typeof.eq_def] <;> simp only
theorem typeof_qdiv_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.qdiv t1 t2) =
      __smtx_typeof_arith_overload_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Real := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Derives `ite_args` from `non_none`. -/
theorem ite_args_of_non_none
    {c t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.ite c t1 t2)) :
    ∃ T : SmtType,
      __smtx_typeof c = SmtType.Bool ∧
        __smtx_typeof t1 = T ∧
        __smtx_typeof t2 = T ∧
        T ≠ SmtType.None := by
  unfold term_has_non_none_type at ht
  rw [typeof_ite_eq] at ht
  let T1 := __smtx_typeof t1
  let T2 := __smtx_typeof t2
  have hBool : __smtx_typeof c = SmtType.Bool := by
    cases hc : __smtx_typeof c <;>
      simp [__smtx_typeof_ite, native_ite, hc] at ht
    simp
  by_cases hEq : native_Teq T1 T2 = true
  · have hT : T1 = T2 := by
      simpa [native_Teq] using hEq
    have hNN : T1 ≠ SmtType.None := by
      simpa [__smtx_typeof_ite, native_ite, hBool, T1, T2, hEq] using ht
    exact ⟨T1, hBool, rfl, by simpa [T1, T2] using hT.symm, hNN⟩
  · exfalso
    apply ht
    simp [__smtx_typeof_ite, native_ite, hBool, T1, T2, hEq]

/-- Shows that evaluating `ite` terms produces values of the expected type. -/
theorem typeof_value_model_eval_ite
    (M : SmtModel)
    (c t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.ite c t1 t2))
    (hpresc : __smtx_typeof_value (__smtx_model_eval M c) = __smtx_typeof c)
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.ite c t1 t2)) =
      __smtx_typeof (SmtTerm.ite c t1 t2) := by
  rcases ite_args_of_non_none ht with ⟨T, hc, h1, h2, hT⟩
  rw [show __smtx_typeof
      (SmtTerm.ite c t1 t2) = T by
    rw [typeof_ite_eq]
    simp [__smtx_typeof_ite, native_ite, native_Teq, hc, h1, h2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rcases bool_value_canonical (by simpa [hc] using hpresc) with ⟨b, hb⟩
  rw [hb]
  cases b
  · simpa [__smtx_model_eval_ite, __smtx_typeof_value, h1, h2] using hpres2
  · simpa [__smtx_model_eval_ite, __smtx_typeof_value, h1, h2] using hpres1

/-- Derives `select_args` from `non_none`. -/
theorem select_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.select t1 t2)) :
    ∃ A B : SmtType,
      __smtx_typeof t1 = SmtType.Map A B ∧
        __smtx_typeof t2 = A := by
  unfold term_has_non_none_type at ht
  rw [typeof_select_eq] at ht
  cases h1 : __smtx_typeof t1 with
  | Map A B =>
      by_cases hEq : native_Teq A (__smtx_typeof t2)
      · have h2' : A = __smtx_typeof t2 := by
          simpa [native_Teq] using hEq
        exact ⟨A, B, rfl, h2'.symm⟩
      · exfalso
        exact ht (by simp [__smtx_typeof_select, native_ite, h1, hEq])
  | _ =>
      exfalso
      exact ht (by simp [__smtx_typeof_select, h1])

/-- Derives `store_args` from `non_none`. -/
theorem store_args_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht : term_has_non_none_type
      (SmtTerm.store t1 t2 t3)) :
    ∃ A B : SmtType,
      __smtx_typeof t1 = SmtType.Map A B ∧
        __smtx_typeof t2 = A ∧
        __smtx_typeof t3 = B := by
  unfold term_has_non_none_type at ht
  rw [typeof_store_eq] at ht
  cases h1 : __smtx_typeof t1 with
  | Map A B =>
      by_cases hEq1 : native_Teq A (__smtx_typeof t2)
      · by_cases hEq2 : native_Teq B (__smtx_typeof t3)
        · have h2' : A = __smtx_typeof t2 := by
            simpa [native_Teq] using hEq1
          have h3' : B = __smtx_typeof t3 := by
            simpa [native_Teq] using hEq2
          exact ⟨A, B, rfl, h2'.symm, h3'.symm⟩
        · exfalso
          exact ht (by
            simp [__smtx_typeof_store, native_ite, h1, hEq1, hEq2])
      · exfalso
        exact ht (by
          simp [__smtx_typeof_store, native_ite, h1, hEq1])
  | _ =>
      exfalso
      exact ht (by simp [__smtx_typeof_store, h1])

/-- Derives `map_diff` argument shapes from `non_none`. -/
theorem map_diff_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.map_diff t1 t2)) :
    (∃ A B : SmtType,
      __smtx_typeof t1 = SmtType.Map A B ∧
        __smtx_typeof t2 = SmtType.Map A B ∧
        __smtx_typeof (SmtTerm.map_diff t1 t2) = A) ∨
    (∃ A : SmtType,
      __smtx_typeof t1 = SmtType.Set A ∧
        __smtx_typeof t2 = SmtType.Set A ∧
        __smtx_typeof (SmtTerm.map_diff t1 t2) = A) := by
  unfold term_has_non_none_type at ht
  rw [typeof_map_diff_eq] at ht
  cases h1 : __smtx_typeof t1 with
  | Map A B =>
      cases h2 : __smtx_typeof t2 with
      | Map A' B' =>
          by_cases hEq : native_and (native_Teq A A') (native_Teq B B')
          · have hEq' : A = A' ∧ B = B' := by
              simpa [native_Teq, SmtEval.native_and] using hEq
            have hAA' : A = A' := hEq'.1
            have hBB' : B = B' := hEq'.2
            subst A'
            subst B'
            left
            refine ⟨A, B, rfl, rfl, ?_⟩
            rw [typeof_map_diff_eq]
            simp [__smtx_typeof_map_diff, h1, h2, native_ite, native_Teq,
              SmtEval.native_and]
          · exfalso
            exact ht (by
              simp [__smtx_typeof_map_diff, h1, h2, native_ite, hEq])
      | _ =>
          exfalso
          exact ht (by simp [__smtx_typeof_map_diff, h1, h2])
  | Set A =>
      cases h2 : __smtx_typeof t2 with
      | Set A' =>
          by_cases hEq : native_Teq A A'
          · have hAA' : A = A' := by
              simpa [native_Teq] using hEq
            subst A'
            right
            refine ⟨A, rfl, rfl, ?_⟩
            rw [typeof_map_diff_eq]
            simp [__smtx_typeof_map_diff, h1, h2, native_ite, native_Teq]
          · exfalso
            exact ht (by
              simp [__smtx_typeof_map_diff, h1, h2, native_ite, hEq])
      | _ =>
          exfalso
          exact ht (by simp [__smtx_typeof_map_diff, h1, h2])
  | _ =>
      exfalso
      exact ht (by simp [__smtx_typeof_map_diff, h1])

private theorem native_eval_map_diff_msm_typed
    {m1 m2 : SmtMap}
    {A B : SmtType}
    (hm1 : __smtx_typeof_map_value m1 = SmtType.Map A B)
    (hm2 : __smtx_typeof_map_value m2 = SmtType.Map A B)
    (hDefault : __smtx_typeof_value (__smtx_type_default A) = A) :
    __smtx_typeof_value (native_eval_map_diff m1 m2) = A := by
  classical
  change __smtx_typeof_value (native_eval_map_diff m1 m2) = A
  rw [hm1, hm2]
  simp [native_ite, native_Teq, SmtEval.native_and]
  by_cases hDiff :
      ∃ i : SmtValue,
        __smtx_typeof_value i = A ∧
          __smtx_value_canonical i = true ∧
          native_veq (__smtx_map_lookup m1 i) (__smtx_map_lookup m2 i) = false
  · simpa [hDiff] using (Classical.choose_spec hDiff).1
  · simpa [hDiff] using hDefault

private theorem native_eval_map_diff_msm_canonical
    {m1 m2 : SmtMap}
    {A B : SmtType}
    (hm1 : __smtx_typeof_map_value m1 = SmtType.Map A B)
    (hm2 : __smtx_typeof_map_value m2 = SmtType.Map A B)
    (hDefault : value_canonical (__smtx_type_default A)) :
    value_canonical (native_eval_map_diff m1 m2) := by
  classical
  change value_canonical (native_eval_map_diff m1 m2)
  rw [hm1, hm2]
  simp [native_ite, native_Teq, SmtEval.native_and]
  by_cases hDiff :
      ∃ i : SmtValue,
        __smtx_typeof_value i = A ∧
          __smtx_value_canonical i = true ∧
          native_veq (__smtx_map_lookup m1 i) (__smtx_map_lookup m2 i) = false
  · have hCan : value_canonical (Classical.choose hDiff) := by
      simpa [value_canonical] using (Classical.choose_spec hDiff).2.1
    simpa [hDiff] using hCan
  · simpa [hDiff] using hDefault

/-- Shows that evaluating `map_diff` terms produces values of the expected index type. -/
theorem typeof_value_model_eval_map_diff
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.map_diff t1 t2))
    (hDefault :
      ∀ {A : SmtType},
        __smtx_typeof (SmtTerm.map_diff t1 t2) = A ->
          __smtx_typeof_value (__smtx_type_default A) = A)
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.map_diff t1 t2)) =
      __smtx_typeof (SmtTerm.map_diff t1 t2) := by
  rcases map_diff_args_of_non_none ht with hMap | hSet
  · rcases hMap with ⟨A, B, h1, h2, hTy⟩
    rw [hTy]
    rw [show __smtx_model_eval M (SmtTerm.map_diff t1 t2) =
        __smtx_model_eval_map_diff (__smtx_model_eval M t1) (__smtx_model_eval M t2) by
      simp [__smtx_model_eval]]
    rcases map_value_canonical (A := A) (B := B)
        (by simpa [h1] using hpres1) with ⟨m1, hm1⟩
    rcases map_value_canonical (A := A) (B := B)
        (by simpa [h2] using hpres2) with ⟨m2, hm2⟩
    rw [hm1, hm2]
    exact native_eval_map_diff_msm_typed
      (by simpa [hm1, h1, __smtx_typeof_value] using hpres1)
      (by simpa [hm2, h2, __smtx_typeof_value] using hpres2)
      (hDefault hTy)
  · rcases hSet with ⟨A, h1, h2, hTy⟩
    rw [hTy]
    rw [show __smtx_model_eval M (SmtTerm.map_diff t1 t2) =
        __smtx_model_eval_map_diff (__smtx_model_eval M t1) (__smtx_model_eval M t2) by
      simp [__smtx_model_eval]]
    rcases set_value_canonical (A := A)
        (by simpa [h1] using hpres1) with ⟨m1, hm1⟩
    rcases set_value_canonical (A := A)
        (by simpa [h2] using hpres2) with ⟨m2, hm2⟩
    have hm1Ty : __smtx_typeof_map_value m1 = SmtType.Map A SmtType.Bool :=
      set_map_value_typed (A := A) (by simpa [hm1, h1] using hpres1)
    have hm2Ty : __smtx_typeof_map_value m2 = SmtType.Map A SmtType.Bool :=
      set_map_value_typed (A := A) (by simpa [hm2, h2] using hpres2)
    rw [hm1, hm2]
    exact native_eval_map_diff_msm_typed hm1Ty hm2Ty (hDefault hTy)

/-- Shows that evaluating `map_diff` terms produces canonical difference witnesses. -/
theorem model_eval_map_diff_canonical
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.map_diff t1 t2))
    (hDefault :
      ∀ {A : SmtType},
        __smtx_typeof (SmtTerm.map_diff t1 t2) = A ->
          value_canonical (__smtx_type_default A))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    value_canonical (__smtx_model_eval M (SmtTerm.map_diff t1 t2)) := by
  rcases map_diff_args_of_non_none ht with hMap | hSet
  · rcases hMap with ⟨A, B, h1, h2, hTy⟩
    rw [show __smtx_model_eval M (SmtTerm.map_diff t1 t2) =
        __smtx_model_eval_map_diff (__smtx_model_eval M t1) (__smtx_model_eval M t2) by
      simp [__smtx_model_eval]]
    rcases map_value_canonical (A := A) (B := B)
        (by simpa [h1] using hpres1) with ⟨m1, hm1⟩
    rcases map_value_canonical (A := A) (B := B)
        (by simpa [h2] using hpres2) with ⟨m2, hm2⟩
    rw [hm1, hm2]
    exact native_eval_map_diff_msm_canonical
      (by simpa [hm1, h1, __smtx_typeof_value] using hpres1)
      (by simpa [hm2, h2, __smtx_typeof_value] using hpres2)
      (hDefault hTy)
  · rcases hSet with ⟨A, h1, h2, hTy⟩
    rw [show __smtx_model_eval M (SmtTerm.map_diff t1 t2) =
        __smtx_model_eval_map_diff (__smtx_model_eval M t1) (__smtx_model_eval M t2) by
      simp [__smtx_model_eval]]
    rcases set_value_canonical (A := A)
        (by simpa [h1] using hpres1) with ⟨m1, hm1⟩
    rcases set_value_canonical (A := A)
        (by simpa [h2] using hpres2) with ⟨m2, hm2⟩
    have hm1Ty : __smtx_typeof_map_value m1 = SmtType.Map A SmtType.Bool :=
      set_map_value_typed (A := A) (by simpa [hm1, h1] using hpres1)
    have hm2Ty : __smtx_typeof_map_value m2 = SmtType.Map A SmtType.Bool :=
      set_map_value_typed (A := A) (by simpa [hm2, h2] using hpres2)
    rw [hm1, hm2]
    exact native_eval_map_diff_msm_canonical hm1Ty hm2Ty (hDefault hTy)

/-- Shows that evaluating `select` terms produces values of the expected type. -/
theorem typeof_value_model_eval_select
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.select t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.select t1 t2)) =
      __smtx_typeof (SmtTerm.select t1 t2) := by
  rcases select_args_of_non_none ht with ⟨A, B, h1, h2⟩
  rw [show __smtx_typeof (SmtTerm.select t1 t2) = B by
    rw [typeof_select_eq]
    simp [__smtx_typeof_select, native_ite, native_Teq, h1, h2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rcases map_value_canonical (A := A) (B := B) (by simpa [h1] using hpres1) with ⟨m, hm⟩
  rw [hm]
  simpa [__smtx_model_eval_select, __smtx_map_select] using
    map_lookup_typed (m := m) (A := A) (B := B) (i := __smtx_model_eval M t2)
            (by simpa [hm, h1, __smtx_typeof_value] using hpres1)
      (by simpa [h2] using hpres2)

/-- Shows that evaluating `store` terms produces values of the expected type. -/
theorem typeof_value_model_eval_store
    (M : SmtModel)
    (t1 t2 t3 : SmtTerm)
    (ht : term_has_non_none_type
      (SmtTerm.store t1 t2 t3))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2)
    (hpres3 : __smtx_typeof_value (__smtx_model_eval M t3) = __smtx_typeof t3) :
    __smtx_typeof_value
        (__smtx_model_eval M (SmtTerm.store t1 t2 t3)) =
      __smtx_typeof (SmtTerm.store t1 t2 t3) := by
  rcases store_args_of_non_none ht with ⟨A, B, h1, h2, h3⟩
  rw [show __smtx_typeof
      (SmtTerm.store t1 t2 t3) =
        SmtType.Map A B by
    rw [typeof_store_eq]
    simp [__smtx_typeof_store, native_ite, native_Teq, h1, h2, h3]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rcases map_value_canonical (A := A) (B := B) (by simpa [h1] using hpres1) with ⟨m, hm⟩
  rw [hm]
  have hMap : __smtx_typeof_map_value m = SmtType.Map A B := by
    simpa [hm, h1, __smtx_typeof_value] using hpres1
  have hi : __smtx_typeof_value (__smtx_model_eval M t2) = A := by
    simpa [h2] using hpres2
  have he : __smtx_typeof_value (__smtx_model_eval M t3) = B := by
    simpa [h3] using hpres3
  simpa [__smtx_model_eval_store, __smtx_map_store, __smtx_typeof_value] using
    map_canon_insert_typed (m := m) (A := A) (B := B) hMap hi he

/-- Derives `eq_term_typeof` from `non_none`. -/
theorem eq_term_typeof_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.eq t1 t2)) :
    __smtx_typeof (SmtTerm.eq t1 t2) = SmtType.Bool := by
  unfold term_has_non_none_type at ht
  rw [typeof_eq_eq] at ht
  rw [typeof_eq_eq]
  cases h1 : __smtx_typeof t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq, h1, h2] at ht ⊢
  all_goals
    first | exact ht

/-- Shows that evaluating `not` terms produces values of the expected type. -/
theorem typeof_value_model_eval_not
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.not t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.not t)) =
      __smtx_typeof (SmtTerm.not t) := by
  have hArg : __smtx_typeof t = SmtType.Bool := by
    unfold term_has_non_none_type at ht
    rw [typeof_not_eq] at ht
    cases h : __smtx_typeof t <;>
      simp [native_ite, native_Teq, h] at ht
    simp
  rw [show __smtx_typeof (SmtTerm.not t) = SmtType.Bool by
    rw [typeof_not_eq]
    simp [native_ite, native_Teq, hArg]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rcases bool_value_canonical (by simpa [hArg] using hpres) with ⟨b, hb⟩
  rw [hb]
  simp [__smtx_model_eval_not, __smtx_typeof_value]

/-- Shows that evaluating `or` terms produces values of the expected type. -/
theorem typeof_value_model_eval_or
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.or t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.or t1 t2)) =
      __smtx_typeof (SmtTerm.or t1 t2) := by
  have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.or) (typeof_or_eq t1 t2) ht
  rw [show __smtx_typeof (SmtTerm.or t1 t2) = SmtType.Bool by
    rw [typeof_or_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rcases bool_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨b1, hb1⟩
  rcases bool_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨b2, hb2⟩
  rw [hb1, hb2]
  simp [__smtx_model_eval_or, __smtx_typeof_value]

/-- Shows that evaluating `and` terms produces values of the expected type. -/
theorem typeof_value_model_eval_and
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.and t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.and t1 t2)) =
      __smtx_typeof (SmtTerm.and t1 t2) := by
  have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.and) (typeof_and_eq t1 t2) ht
  rw [show __smtx_typeof (SmtTerm.and t1 t2) = SmtType.Bool by
    rw [typeof_and_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rcases bool_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨b1, hb1⟩
  rcases bool_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨b2, hb2⟩
  rw [hb1, hb2]
  simp [__smtx_model_eval_and, __smtx_typeof_value]

/-- Shows that evaluating `imp` terms produces values of the expected type. -/
theorem typeof_value_model_eval_imp
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.imp t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.imp t1 t2)) =
      __smtx_typeof (SmtTerm.imp t1 t2) := by
  have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.imp) (typeof_imp_eq t1 t2) ht
  rw [show __smtx_typeof (SmtTerm.imp t1 t2) = SmtType.Bool by
    rw [typeof_imp_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rcases bool_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨b1, hb1⟩
  rcases bool_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨b2, hb2⟩
  rw [hb1, hb2]
  simp [__smtx_model_eval_imp, __smtx_model_eval_or, __smtx_model_eval_not, __smtx_typeof_value]

/-- Shows that evaluating `eq` terms produces values of the expected type. -/
theorem typeof_value_model_eval_eq
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.eq t1 t2)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.eq t1 t2)) =
      __smtx_typeof (SmtTerm.eq t1 t2) := by
  rw [eq_term_typeof_of_non_none ht]
  rw [__smtx_model_eval.eq_def] <;> simp only
  simpa using
    typeof_value_model_eval_eq_value
      (__smtx_model_eval M t1) (__smtx_model_eval M t2)

/-- Shows that evaluating `xor` terms produces values of the expected type. -/
theorem typeof_value_model_eval_xor
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.xor t1 t2)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.xor t1 t2)) =
      __smtx_typeof (SmtTerm.xor t1 t2) := by
  have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.xor) (typeof_xor_eq t1 t2) ht
  rw [show __smtx_typeof (SmtTerm.xor t1 t2) = SmtType.Bool by
    rw [typeof_xor_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  simpa using typeof_value_model_eval_xor_value (__smtx_model_eval M t1) (__smtx_model_eval M t2)

/-- Shows that evaluating `plus` terms produces values of the expected type. -/
theorem typeof_value_model_eval_plus
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.plus t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.plus t1 t2)) =
      __smtx_typeof (SmtTerm.plus t1 t2) := by
  rcases arith_binop_args_of_non_none (op := SmtTerm.plus) (typeof_plus_eq t1 t2) ht with hArgs | hArgs
  · rw [show __smtx_typeof (SmtTerm.plus t1 t2) = SmtType.Int by
      rw [typeof_plus_eq]
      simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]]
    rw [__smtx_model_eval.eq_def] <;> simp only
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (SmtTerm.plus t1 t2) = SmtType.Real by
      rw [typeof_plus_eq]
      simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]]
    rw [__smtx_model_eval.eq_def] <;> simp only
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

/-- Shows that evaluating `neg` terms produces values of the expected type. -/
theorem typeof_value_model_eval_neg
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.neg t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.neg t1 t2)) =
      __smtx_typeof (SmtTerm.neg t1 t2) := by
  rcases arith_binop_args_of_non_none (op := SmtTerm.neg) (typeof_neg_eq t1 t2) ht with hArgs | hArgs
  · rw [show __smtx_typeof (SmtTerm.neg t1 t2) = SmtType.Int by
      rw [typeof_neg_eq]
      simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]]
    rw [__smtx_model_eval.eq_def] <;> simp only
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (SmtTerm.neg t1 t2) = SmtType.Real by
      rw [typeof_neg_eq]
      simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]]
    rw [__smtx_model_eval.eq_def] <;> simp only
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

/-- Shows that evaluating `mult` terms produces values of the expected type. -/
theorem typeof_value_model_eval_mult
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.mult t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.mult t1 t2)) =
      __smtx_typeof (SmtTerm.mult t1 t2) := by
  rcases arith_binop_args_of_non_none (op := SmtTerm.mult) (typeof_mult_eq t1 t2) ht with hArgs | hArgs
  · rw [show __smtx_typeof (SmtTerm.mult t1 t2) = SmtType.Int by
      rw [typeof_mult_eq]
      simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]]
    rw [__smtx_model_eval.eq_def] <;> simp only
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (SmtTerm.mult t1 t2) = SmtType.Real by
      rw [typeof_mult_eq]
      simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]]
    rw [__smtx_model_eval.eq_def] <;> simp only
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

/-- Shows that evaluating `lt` terms produces values of the expected type. -/
theorem typeof_value_model_eval_lt
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.lt t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.lt t1 t2)) =
      __smtx_typeof (SmtTerm.lt t1 t2) := by
  rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.lt) (typeof_lt_eq t1 t2) ht with hArgs | hArgs
  · rw [show __smtx_typeof (SmtTerm.lt t1 t2) = SmtType.Bool by
      rw [typeof_lt_eq]
      simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    rw [__smtx_model_eval.eq_def] <;> simp only
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (SmtTerm.lt t1 t2) = SmtType.Bool by
      rw [typeof_lt_eq]
      simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    rw [__smtx_model_eval.eq_def] <;> simp only
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

/-- Shows that evaluating `leq` terms produces values of the expected type. -/
theorem typeof_value_model_eval_leq
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.leq t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.leq t1 t2)) =
      __smtx_typeof (SmtTerm.leq t1 t2) := by
  rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.leq) (typeof_leq_eq t1 t2) ht with hArgs | hArgs
  · rw [show __smtx_typeof (SmtTerm.leq t1 t2) = SmtType.Bool by
      rw [typeof_leq_eq]
      simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    rw [__smtx_model_eval.eq_def] <;> simp only
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (SmtTerm.leq t1 t2) = SmtType.Bool by
      rw [typeof_leq_eq]
      simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    rw [__smtx_model_eval.eq_def] <;> simp only
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

/-- Shows that evaluating `gt` terms produces values of the expected type. -/
theorem typeof_value_model_eval_gt
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.gt t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.gt t1 t2)) =
      __smtx_typeof (SmtTerm.gt t1 t2) := by
  rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.gt) (typeof_gt_eq t1 t2) ht with hArgs | hArgs
  · rw [show __smtx_typeof (SmtTerm.gt t1 t2) = SmtType.Bool by
      rw [typeof_gt_eq]
      simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    rw [__smtx_model_eval.eq_def] <;> simp only
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (SmtTerm.gt t1 t2) = SmtType.Bool by
      rw [typeof_gt_eq]
      simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    rw [__smtx_model_eval.eq_def] <;> simp only
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

/-- Shows that evaluating `geq` terms produces values of the expected type. -/
theorem typeof_value_model_eval_geq
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.geq t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.geq t1 t2)) =
      __smtx_typeof (SmtTerm.geq t1 t2) := by
  rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.geq) (typeof_geq_eq t1 t2) ht with hArgs | hArgs
  · rw [show __smtx_typeof (SmtTerm.geq t1 t2) = SmtType.Bool by
      rw [typeof_geq_eq]
      simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    rw [__smtx_model_eval.eq_def] <;> simp only
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (SmtTerm.geq t1 t2) = SmtType.Bool by
      rw [typeof_geq_eq]
      simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    rw [__smtx_model_eval.eq_def] <;> simp only
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

/-- Shows that evaluating `to_real` terms produces values of the expected type. -/
theorem typeof_value_model_eval_to_real
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.to_real t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.to_real t)) =
      __smtx_typeof (SmtTerm.to_real t) := by
  have hArg := to_real_arg_of_non_none ht
  rw [show __smtx_typeof (SmtTerm.to_real t) = SmtType.Real by
    rw [typeof_to_real_eq]
    simp [native_ite, native_Teq, hArg]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rcases int_value_canonical (by simpa [hArg] using hpres) with ⟨n, hn⟩
  rw [hn]
  rfl

/-- Shows that evaluating `to_int` terms produces values of the expected type. -/
theorem typeof_value_model_eval_to_int
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.to_int t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.to_int t)) =
      __smtx_typeof (SmtTerm.to_int t) := by
  have hArg : __smtx_typeof t = SmtType.Real :=
    real_arg_of_non_none (op := SmtTerm.to_int) (typeof_to_int_eq t) ht
  rw [show __smtx_typeof (SmtTerm.to_int t) = SmtType.Int by
    rw [typeof_to_int_eq]
    simp [native_ite, native_Teq, hArg]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rcases real_value_canonical (by simpa [hArg] using hpres) with ⟨q, hq⟩
  rw [hq]
  rfl

/-- Shows that evaluating `is_int` terms produces values of the expected type. -/
theorem typeof_value_model_eval_is_int
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.is_int t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.is_int t)) =
      __smtx_typeof (SmtTerm.is_int t) := by
  have hArg : __smtx_typeof t = SmtType.Real :=
    real_arg_of_non_none (op := SmtTerm.is_int) (typeof_is_int_eq t) ht
  rw [show __smtx_typeof (SmtTerm.is_int t) = SmtType.Bool by
    rw [typeof_is_int_eq]
    simp [native_ite, native_Teq, hArg]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rcases real_value_canonical (by simpa [hArg] using hpres) with ⟨q, hq⟩
  rw [hq]
  simpa [__smtx_model_eval_is_int, __smtx_model_eval_to_int, __smtx_model_eval_to_real] using
    typeof_value_model_eval_eq_value
      (SmtValue.Rational (native_to_real (native_to_int q))) (SmtValue.Rational q)

/-- Shows that evaluating `abs` terms produces values of the expected type. -/
theorem typeof_value_model_eval_abs
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.abs t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.abs t)) =
      __smtx_typeof (SmtTerm.abs t) := by
  rcases abs_arg_of_non_none ht with hArg | hArg
  · rw [show __smtx_typeof (SmtTerm.abs t) = SmtType.Int by
      rw [typeof_abs_eq]
      simp [__smtx_typeof_arith_overload_op_1, hArg]]
    rw [__smtx_model_eval.eq_def] <;> simp only
    rcases int_value_canonical (by simpa [hArg] using hpres) with ⟨n, hn⟩
    rw [hn]
    rfl
  · rw [show __smtx_typeof (SmtTerm.abs t) = SmtType.Real by
      rw [typeof_abs_eq]
      simp [__smtx_typeof_arith_overload_op_1, hArg]]
    rw [__smtx_model_eval.eq_def] <;> simp only
    rcases real_value_canonical (by simpa [hArg] using hpres) with ⟨q, hq⟩
    rw [hq]
    rfl

/-- Shows that evaluating `uneg` terms produces values of the expected type. -/
theorem typeof_value_model_eval_uneg
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.uneg t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.uneg t)) =
      __smtx_typeof (SmtTerm.uneg t) := by
  rcases arith_unop_arg_of_non_none (op := SmtTerm.uneg) (typeof_uneg_eq t) ht with hArg | hArg
  · rw [show __smtx_typeof (SmtTerm.uneg t) = SmtType.Int by
      rw [typeof_uneg_eq]
      simp [__smtx_typeof_arith_overload_op_1, hArg]]
    rw [__smtx_model_eval.eq_def] <;> simp only
    rcases int_value_canonical (by simpa [hArg] using hpres) with ⟨n, hn⟩
    rw [hn]
    rfl
  · rw [show __smtx_typeof (SmtTerm.uneg t) = SmtType.Real by
      rw [typeof_uneg_eq]
      simp [__smtx_typeof_arith_overload_op_1, hArg]]
    rw [__smtx_model_eval.eq_def] <;> simp only
    rcases real_value_canonical (by simpa [hArg] using hpres) with ⟨q, hq⟩
    rw [hq]
    rfl

/-- Derives `int_ret_arg` from `non_none`. -/
theorem int_ret_arg_of_non_none
    {op : SmtTerm -> SmtTerm}
    {t : SmtTerm}
    {R : SmtType}
    (hTy :
      __smtx_typeof (op t) =
        native_ite (native_Teq (__smtx_typeof t) SmtType.Int) R SmtType.None)
    (ht : term_has_non_none_type (op t)) :
    __smtx_typeof t = SmtType.Int := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t <;>
    simp [hTy, native_ite, native_Teq, h] at ht
  simp

/-- Derives `int_binop_args` from `non_none`. -/
theorem int_binop_args_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    {R : SmtType}
    (hTy :
      __smtx_typeof (op t1 t2) =
        native_ite (native_Teq (__smtx_typeof t1) SmtType.Int)
          (native_ite (native_Teq (__smtx_typeof t2) SmtType.Int) R SmtType.None)
          SmtType.None)
    (ht : term_has_non_none_type (op t1 t2)) :
    __smtx_typeof t1 = SmtType.Int ∧ __smtx_typeof t2 = SmtType.Int := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [hTy, native_ite, native_Teq, h1, h2] at ht
  simp

/-- The integer-to-integer native-function type used for arithmetic defaults is well formed. -/
theorem fun_type_wf_int_int :
    __smtx_type_wf (SmtType.FunType SmtType.Int SmtType.Int) = true := by
  simp [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
    native_and, native_inhabited_type_int]

/-- The real-to-real native-function type used for arithmetic defaults is well formed. -/
theorem fun_type_wf_real_real :
    __smtx_type_wf (SmtType.FunType SmtType.Real SmtType.Real) = true := by
  simp [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
    native_and, native_inhabited_type_real]

/-- Shows that evaluating `apply_lookup_fun` terms produces values of the expected type. -/
theorem typeof_value_model_eval_apply_lookup_fun
    (M : SmtModel)
    (hM : model_wf M)
    (s : native_String)
    (A B : SmtType)
    (hA : A ≠ SmtType.None)
    (hB : type_inhabited B)
    (hFunWF : __smtx_type_wf (SmtType.FunType A B) = true)
    (i : SmtValue)
    (hi : __smtx_typeof_value i = A) :
    __smtx_typeof_value
        (__smtx_model_eval_apply M (native_model_lookup M s (SmtType.FunType A B)) i) = B := by
  have hLookup :
      __smtx_typeof_value (native_model_lookup M s (SmtType.FunType A B)) =
        SmtType.FunType A B :=
    model_total_typed_lookup hM s (SmtType.FunType A B) hFunWF
  exact typeof_value_model_eval_apply_fun_value M hM hA hFunWF hLookup hi

theorem typeof_value_model_eval_div_total
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.div_total t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.div_total t1 t2)) =
      __smtx_typeof (SmtTerm.div_total t1 t2) := by
  have hArgs := int_binop_args_of_non_none (op := SmtTerm.div_total) (typeof_div_total_eq t1 t2) ht
  rw [show __smtx_typeof (SmtTerm.div_total t1 t2) = SmtType.Int by
    rw [typeof_div_total_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
  rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
  rw [hn1, hn2]
  rfl

/-- Shows that evaluating `mod_total` terms produces values of the expected type. -/
theorem typeof_value_model_eval_mod_total
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.mod_total t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.mod_total t1 t2)) =
      __smtx_typeof (SmtTerm.mod_total t1 t2) := by
  have hArgs := int_binop_args_of_non_none (op := SmtTerm.mod_total) (typeof_mod_total_eq t1 t2) ht
  rw [show __smtx_typeof (SmtTerm.mod_total t1 t2) = SmtType.Int by
    rw [typeof_mod_total_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
  rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
  rw [hn1, hn2]
  rfl

/-- Shows that evaluating `divisible` terms produces values of the expected type. -/
theorem typeof_value_model_eval_divisible
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.divisible t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.divisible t1 t2)) =
      __smtx_typeof (SmtTerm.divisible t1 t2) := by
  have hArgs := int_binop_args_of_non_none (op := SmtTerm.divisible) (typeof_divisible_eq t1 t2) ht
  rw [show __smtx_typeof (SmtTerm.divisible t1 t2) = SmtType.Bool by
    rw [typeof_divisible_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
  rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
  rw [hn1, hn2]
  simpa [__smtx_model_eval_divisible, __smtx_model_eval_mod_total] using
    typeof_value_model_eval_eq_value
      (SmtValue.Numeral (native_mod_total n2 n1))
      (SmtValue.Numeral 0)

/-- Shows that evaluating `int_pow2` terms produces values of the expected type. -/
theorem typeof_value_model_eval_int_pow2
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.int_pow2 t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.int_pow2 t)) =
      __smtx_typeof (SmtTerm.int_pow2 t) := by
  have hArg : __smtx_typeof t = SmtType.Int :=
    int_ret_arg_of_non_none (op := SmtTerm.int_pow2) (typeof_int_pow2_eq t) ht
  rw [show __smtx_typeof (SmtTerm.int_pow2 t) = SmtType.Int by
    rw [typeof_int_pow2_eq]
    simp [native_ite, native_Teq, hArg]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rcases int_value_canonical (by simpa [hArg] using hpres) with ⟨n, hn⟩
  rw [hn]
  rfl

/-- Shows that evaluating `int_log2` terms produces values of the expected type. -/
theorem typeof_value_model_eval_int_log2
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.int_log2 t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.int_log2 t)) =
      __smtx_typeof (SmtTerm.int_log2 t) := by
  have hArg : __smtx_typeof t = SmtType.Int :=
    int_ret_arg_of_non_none (op := SmtTerm.int_log2) (typeof_int_log2_eq t) ht
  rw [show __smtx_typeof (SmtTerm.int_log2 t) = SmtType.Int by
    rw [typeof_int_log2_eq]
    simp [native_ite, native_Teq, hArg]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rcases int_value_canonical (by simpa [hArg] using hpres) with ⟨n, hn⟩
  rw [hn]
  rfl

/-- Shows that evaluating `div` terms produces values of the expected type. -/
theorem typeof_value_model_eval_div
    (M : SmtModel)
    (hM : model_wf M)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.div t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.div t1 t2)) =
      __smtx_typeof (SmtTerm.div t1 t2) := by
  have hArgs := int_binop_args_of_non_none (op := SmtTerm.div) (typeof_div_eq t1 t2) ht
  rw [show __smtx_typeof (SmtTerm.div t1 t2) = SmtType.Int by
    rw [typeof_div_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
  rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
  rw [hn1, hn2]
  by_cases hZero : n2 = 0
  · simpa [__smtx_model_eval_ite, __smtx_model_eval_eq, __smtx_model_eval_div_total,
      native_veq, hZero] using
      typeof_value_model_eval_apply_lookup_fun M hM
        native_div_by_zero_id SmtType.Int SmtType.Int (by simp) type_inhabited_int fun_type_wf_int_int
        (SmtValue.Numeral n1) rfl
  · simp [__smtx_model_eval_ite, __smtx_model_eval_eq, __smtx_model_eval_div_total,
      __smtx_typeof_value, native_veq, hZero]

/-- Shows that evaluating `mod` terms produces values of the expected type. -/
theorem typeof_value_model_eval_mod
    (M : SmtModel)
    (hM : model_wf M)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.mod t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.mod t1 t2)) =
      __smtx_typeof (SmtTerm.mod t1 t2) := by
  have hArgs := int_binop_args_of_non_none (op := SmtTerm.mod) (typeof_mod_eq t1 t2) ht
  rw [show __smtx_typeof (SmtTerm.mod t1 t2) = SmtType.Int by
    rw [typeof_mod_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
  rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
  rw [hn1, hn2]
  by_cases hZero : n2 = 0
  · simpa [__smtx_model_eval_ite, __smtx_model_eval_eq, __smtx_model_eval_mod_total,
      native_veq, hZero] using
      typeof_value_model_eval_apply_lookup_fun M hM
        native_mod_by_zero_id SmtType.Int SmtType.Int (by simp) type_inhabited_int fun_type_wf_int_int
        (SmtValue.Numeral n1) rfl
  · simp [__smtx_model_eval_ite, __smtx_model_eval_eq, __smtx_model_eval_mod_total,
      __smtx_typeof_value, native_veq, hZero]

/-- Shows that evaluating `qdiv_total` terms produces values of the expected type. -/
theorem typeof_value_model_eval_qdiv_total
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.qdiv_total t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.qdiv_total t1 t2)) =
      __smtx_typeof (SmtTerm.qdiv_total t1 t2) := by
  rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv_total) (typeof_qdiv_total_eq t1 t2) ht with hArgs | hArgs
  · rw [show __smtx_typeof (SmtTerm.qdiv_total t1 t2) = SmtType.Real by
      rw [typeof_qdiv_total_eq]
      simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    rw [__smtx_model_eval.eq_def] <;> simp only
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (SmtTerm.qdiv_total t1 t2) = SmtType.Real by
      rw [typeof_qdiv_total_eq]
      simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    rw [__smtx_model_eval.eq_def] <;> simp only
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

/-- Shows that evaluating `qdiv` terms produces values of the expected type. -/
theorem typeof_value_model_eval_qdiv
    (M : SmtModel)
    (hM : model_wf M)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.qdiv t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.qdiv t1 t2)) =
      __smtx_typeof (SmtTerm.qdiv t1 t2) := by
  rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv) (typeof_qdiv_eq t1 t2) ht with hArgs | hArgs
  · rw [show __smtx_typeof (SmtTerm.qdiv t1 t2) = SmtType.Real by
      rw [typeof_qdiv_eq]
      simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    rw [__smtx_model_eval.eq_def] <;> simp only
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    by_cases hZero : native_to_real n2 = native_mk_rational 0 1
    · simpa [__smtx_model_eval_ite, __smtx_model_eval_eq, __smtx_to_real_coerce,
        __smtx_model_eval_qdiv_total, native_veq, hZero] using
        typeof_value_model_eval_apply_lookup_fun M hM
          native_qdiv_by_zero_id SmtType.Real SmtType.Real (by simp) type_inhabited_real fun_type_wf_real_real
          (SmtValue.Rational (native_to_real n1)) rfl
    · simp [__smtx_model_eval_ite, __smtx_model_eval_eq, __smtx_to_real_coerce,
        __smtx_model_eval_qdiv_total, __smtx_typeof_value, native_veq, hZero]
  · rw [show __smtx_typeof (SmtTerm.qdiv t1 t2) = SmtType.Real by
      rw [typeof_qdiv_eq]
      simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    rw [__smtx_model_eval.eq_def] <;> simp only
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    by_cases hZero : q2 = native_mk_rational 0 1
    · simpa [__smtx_model_eval_ite, __smtx_model_eval_eq, __smtx_to_real_coerce,
        __smtx_model_eval_qdiv_total, native_veq, hZero] using
        typeof_value_model_eval_apply_lookup_fun M hM
          native_qdiv_by_zero_id SmtType.Real SmtType.Real (by simp) type_inhabited_real fun_type_wf_real_real
          (SmtValue.Rational q1) rfl
    · simp [__smtx_model_eval_ite, __smtx_model_eval_eq, __smtx_to_real_coerce,
        __smtx_model_eval_qdiv_total, __smtx_typeof_value, native_veq, hZero]

end Smtm
