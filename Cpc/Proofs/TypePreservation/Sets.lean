module

public import Cpc.Proofs.TypePreservation.Helpers
import all Cpc.SmtModel
import all Cpc.Proofs.TypePreservation.Common

public section

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

/-- Rewrites the typing equation for `set_union`. -/
theorem typeof_set_union_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.set_union t1 t2) =
      __smtx_typeof_sets_op_2 (__smtx_typeof t1) (__smtx_typeof t2) := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Rewrites the typing equation for `set_inter`. -/
theorem typeof_set_inter_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.set_inter t1 t2) =
      __smtx_typeof_sets_op_2 (__smtx_typeof t1) (__smtx_typeof t2) := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Rewrites the typing equation for `set_minus`. -/
theorem typeof_set_minus_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.set_minus t1 t2) =
      __smtx_typeof_sets_op_2 (__smtx_typeof t1) (__smtx_typeof t2) := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Rewrites the typing equation for `set_member`. -/
theorem typeof_set_member_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.set_member t1 t2) =
      __smtx_typeof_set_member (__smtx_typeof t1) (__smtx_typeof t2) := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Rewrites the typing equation for `set_subset`. -/
theorem typeof_set_subset_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.set_subset t1 t2) =
      __smtx_typeof_sets_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Derives `set_binop_args` from `non_none`. -/
theorem set_binop_args_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_sets_op_2 (__smtx_typeof t1) (__smtx_typeof t2))
    (ht : term_has_non_none_type (op t1 t2)) :
    ∃ A : SmtType,
      __smtx_typeof t1 = SmtType.Set A ∧
        __smtx_typeof t2 = SmtType.Set A := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | Set A =>
      cases h2 : __smtx_typeof t2 with
      | Set C =>
          by_cases hEq : A = C
          · subst hEq
            exact ⟨A, rfl, rfl⟩
          · simp [hTy, __smtx_typeof_sets_op_2, native_ite, native_Teq, h1, h2, hEq] at ht
      | _ =>
          simp [hTy, __smtx_typeof_sets_op_2, h1, h2] at ht
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [hTy, __smtx_typeof_sets_op_2, h1, h2] at ht

/-- Derives `set_binop_ret_args` from `non_none`. -/
theorem set_binop_ret_args_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {t1 t2 : SmtTerm} {T : SmtType}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_sets_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) T)
    (ht : term_has_non_none_type (op t1 t2)) :
    ∃ A : SmtType,
      __smtx_typeof t1 = SmtType.Set A ∧
        __smtx_typeof t2 = SmtType.Set A := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | Set A =>
      cases h2 : __smtx_typeof t2 with
      | Set C =>
          by_cases hEq : A = C
          · subst hEq
            exact ⟨A, rfl, rfl⟩
          · simp [hTy, __smtx_typeof_sets_op_2_ret, native_ite, native_Teq, h1, h2, hEq] at ht
      | _ =>
          simp [hTy, __smtx_typeof_sets_op_2_ret, h1, h2] at ht
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [hTy, __smtx_typeof_sets_op_2_ret, h1, h2] at ht

/-- Derives `set_member_args` from `non_none`. -/
theorem set_member_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.set_member t1 t2)) :
    ∃ A : SmtType,
      __smtx_typeof t1 = A ∧
        __smtx_typeof t2 = SmtType.Set A := by
  unfold term_has_non_none_type at ht
  rw [typeof_set_member_eq] at ht
  cases h2 : __smtx_typeof t2 with
  | Set A =>
      by_cases hEq : __smtx_typeof t1 = A
      · refine ⟨A, hEq, ?_⟩
        rfl
      · simp [__smtx_typeof_set_member, native_ite, native_Teq, h2, hEq] at ht
  | _ =>
      simp [__smtx_typeof_set_member, h2] at ht

/-- Lemma about `mss_op_internal_typed`. -/
theorem mss_op_internal_typed
    (isInter : native_Bool) :
    ∀ {m1 m2 acc : SmtMap} {A : SmtType},
      __smtx_typeof_map_value m1 = SmtType.Map A SmtType.Bool ->
        __smtx_typeof_map_value m2 = SmtType.Map A SmtType.Bool ->
        __smtx_typeof_map_value acc = SmtType.Map A SmtType.Bool ->
        __smtx_typeof_map_value (__smtx_set_op_rec isInter m1 m2 acc) =
          SmtType.Map A SmtType.Bool
  | SmtMap.default T efalse, m2, acc, A, hm1, hm2, hacc => by
      simpa [__smtx_set_op_rec] using hacc
  | SmtMap.cons e etrue m1, m2, acc, A, hm1, hm2, hacc => by
      by_cases hEq :
          native_Teq (SmtType.Map (__smtx_typeof_value e) (__smtx_typeof_value etrue))
            (__smtx_typeof_map_value m1)
      · have hm1' : __smtx_typeof_map_value m1 = SmtType.Map A SmtType.Bool := by
          simpa [__smtx_typeof_map_value, native_ite, hEq] using hm1
        have hEq' :
            SmtType.Map (__smtx_typeof_value e) (__smtx_typeof_value etrue) =
              __smtx_typeof_map_value m1 := by
          simpa [native_Teq] using hEq
        have hHead :
            SmtType.Map (__smtx_typeof_value e) (__smtx_typeof_value etrue) =
              SmtType.Map A SmtType.Bool := hEq'.trans hm1'
        have he : __smtx_typeof_value e = A := by
          simpa [__smtx_index_typeof_map] using congrArg __smtx_index_typeof_map hHead
        have hAccCons :
            __smtx_typeof_map_value
                (__smtx_map_update_aux (__smtx_map_get_default acc) acc e
                  (SmtValue.Boolean true)) =
              SmtType.Map A SmtType.Bool := by
          exact map_canon_insert_typed (m := acc) (A := A) (B := SmtType.Bool)
            hacc he rfl
        let acc' :=
          native_ite
              (native_iff
                (native_veq (__smtx_map_lookup m2 e) (SmtValue.Boolean true))
                isInter)
            (__smtx_map_update_aux (__smtx_map_get_default acc) acc e
              (SmtValue.Boolean true)) acc
        have hacc' : __smtx_typeof_map_value acc' = SmtType.Map A SmtType.Bool := by
          dsimp [acc']
          by_cases hKeep :
              native_iff
                (native_veq (__smtx_map_lookup m2 e) (SmtValue.Boolean true))
                isInter
          · simpa [native_ite, hKeep] using hAccCons
          · simpa [native_ite, hKeep] using hacc
        simpa [__smtx_set_op_rec, hEq, acc'] using
          mss_op_internal_typed isInter (m1 := m1) (m2 := m2) (acc := acc')
            (A := A) hm1' hm2 hacc'
      · simp [__smtx_typeof_map_value, native_ite, hEq] at hm1

/-- Shows that evaluating `set_union` terms produces values of the expected type. -/
theorem typeof_value_model_eval_set_union
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.set_union t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.set_union t1 t2)) =
      __smtx_typeof (SmtTerm.set_union t1 t2) := by
  rcases set_binop_args_of_non_none (op := SmtTerm.set_union) (typeof_set_union_eq t1 t2) ht with
    ⟨A, h1, h2⟩
  rw [show __smtx_typeof (SmtTerm.set_union t1 t2) =
      SmtType.Set A by
    rw [typeof_set_union_eq]
    simp [__smtx_typeof_sets_op_2, native_ite, native_Teq, h1, h2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value (__smtx_model_eval_set_union (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.Set A
  rcases set_value_canonical (A := A)
      (by simpa [h1] using hpres1) with ⟨m1, hm1⟩
  rcases set_value_canonical (A := A)
      (by simpa [h2] using hpres2) with ⟨m2, hm2⟩
  have hm1Ty : __smtx_typeof_map_value m1 = SmtType.Map A SmtType.Bool := by
    apply set_map_value_typed (A := A)
    simpa [hm1, h1] using hpres1
  have hm2Ty : __smtx_typeof_map_value m2 = SmtType.Map A SmtType.Bool := by
    apply set_map_value_typed (A := A)
    simpa [hm2, h2] using hpres2
  have hIdx1 : __smtx_index_typeof_map (__smtx_typeof_map_value m1) = A := by
    simpa [__smtx_index_typeof_map] using congrArg __smtx_index_typeof_map hm1Ty
  have hDefault :
      __smtx_typeof_map_value (SmtMap.default A (SmtValue.Boolean false)) =
        SmtType.Map A SmtType.Bool := by
    simp [__smtx_typeof_map_value, __smtx_typeof_value]
  rw [hm1, hm2]
  have hRes :
      __smtx_typeof_map_value
          (__smtx_set_op_rec false m1 (SmtMap.default A (SmtValue.Boolean false)) m2) =
        SmtType.Map A SmtType.Bool := by
    exact mss_op_internal_typed false
      (m1 := m1) (m2 := SmtMap.default A (SmtValue.Boolean false)) (acc := m2)
      (A := A)
      hm1Ty
      hDefault
      hm2Ty
  simp [__smtx_model_eval_set_union, __smtx_set_union, __smtx_typeof_value,
    __smtx_map_to_set_type, hIdx1, hRes]

/-- Shows that evaluating `set_inter` terms produces values of the expected type. -/
theorem typeof_value_model_eval_set_inter
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.set_inter t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.set_inter t1 t2)) =
      __smtx_typeof (SmtTerm.set_inter t1 t2) := by
  rcases set_binop_args_of_non_none (op := SmtTerm.set_inter) (typeof_set_inter_eq t1 t2) ht with
    ⟨A, h1, h2⟩
  rw [show __smtx_typeof (SmtTerm.set_inter t1 t2) =
      SmtType.Set A by
    rw [typeof_set_inter_eq]
    simp [__smtx_typeof_sets_op_2, native_ite, native_Teq, h1, h2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value (__smtx_model_eval_set_inter (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.Set A
  rcases set_value_canonical (A := A)
      (by simpa [h1] using hpres1) with ⟨m1, hm1⟩
  rcases set_value_canonical (A := A)
      (by simpa [h2] using hpres2) with ⟨m2, hm2⟩
  have hm1Ty : __smtx_typeof_map_value m1 = SmtType.Map A SmtType.Bool := by
    apply set_map_value_typed (A := A)
    simpa [hm1, h1] using hpres1
  have hm2Ty : __smtx_typeof_map_value m2 = SmtType.Map A SmtType.Bool := by
    apply set_map_value_typed (A := A)
    simpa [hm2, h2] using hpres2
  have hIdx1 : __smtx_index_typeof_map (__smtx_typeof_map_value m1) = A := by
    simpa [__smtx_index_typeof_map] using congrArg __smtx_index_typeof_map hm1Ty
  have hDefault :
      __smtx_typeof_map_value (SmtMap.default A (SmtValue.Boolean false)) =
        SmtType.Map A SmtType.Bool := by
    simp [__smtx_typeof_map_value, __smtx_typeof_value]
  rw [hm1, hm2]
  have hRes :
      __smtx_typeof_map_value
          (__smtx_set_op_rec true m1 m2 (SmtMap.default A (SmtValue.Boolean false))) =
        SmtType.Map A SmtType.Bool := by
    exact mss_op_internal_typed true
      (m1 := m1) (m2 := m2) (acc := SmtMap.default A (SmtValue.Boolean false))
      (A := A)
      hm1Ty
      hm2Ty
      hDefault
  simp [__smtx_model_eval_set_inter, __smtx_set_inter, __smtx_typeof_value,
    __smtx_map_to_set_type, hIdx1, hRes]

/-- Shows that evaluating `set_minus` terms produces values of the expected type. -/
theorem typeof_value_model_eval_set_minus
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.set_minus t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.set_minus t1 t2)) =
      __smtx_typeof (SmtTerm.set_minus t1 t2) := by
  rcases set_binop_args_of_non_none (op := SmtTerm.set_minus) (typeof_set_minus_eq t1 t2) ht with
    ⟨A, h1, h2⟩
  rw [show __smtx_typeof (SmtTerm.set_minus t1 t2) =
      SmtType.Set A by
    rw [typeof_set_minus_eq]
    simp [__smtx_typeof_sets_op_2, native_ite, native_Teq, h1, h2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value (__smtx_model_eval_set_minus (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.Set A
  rcases set_value_canonical (A := A)
      (by simpa [h1] using hpres1) with ⟨m1, hm1⟩
  rcases set_value_canonical (A := A)
      (by simpa [h2] using hpres2) with ⟨m2, hm2⟩
  have hm1Ty : __smtx_typeof_map_value m1 = SmtType.Map A SmtType.Bool := by
    apply set_map_value_typed (A := A)
    simpa [hm1, h1] using hpres1
  have hm2Ty : __smtx_typeof_map_value m2 = SmtType.Map A SmtType.Bool := by
    apply set_map_value_typed (A := A)
    simpa [hm2, h2] using hpres2
  have hIdx1 : __smtx_index_typeof_map (__smtx_typeof_map_value m1) = A := by
    simpa [__smtx_index_typeof_map] using congrArg __smtx_index_typeof_map hm1Ty
  have hDefault :
      __smtx_typeof_map_value (SmtMap.default A (SmtValue.Boolean false)) =
        SmtType.Map A SmtType.Bool := by
    simp [__smtx_typeof_map_value, __smtx_typeof_value]
  rw [hm1, hm2]
  have hRes :
      __smtx_typeof_map_value
          (__smtx_set_op_rec false m1 m2 (SmtMap.default A (SmtValue.Boolean false))) =
        SmtType.Map A SmtType.Bool := by
    exact mss_op_internal_typed false
      (m1 := m1) (m2 := m2) (acc := SmtMap.default A (SmtValue.Boolean false))
      (A := A)
      hm1Ty
      hm2Ty
      hDefault
  simp [__smtx_model_eval_set_minus, __smtx_set_minus, __smtx_typeof_value,
    __smtx_map_to_set_type, hIdx1, hRes]

/-- Shows that evaluating `set_member` terms produces values of the expected type. -/
theorem typeof_value_model_eval_set_member
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.set_member t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.set_member t1 t2)) =
      __smtx_typeof (SmtTerm.set_member t1 t2) := by
  rcases set_member_args_of_non_none ht with ⟨A, h1, h2⟩
  rw [show __smtx_typeof (SmtTerm.set_member t1 t2) =
      SmtType.Bool by
    rw [typeof_set_member_eq]
    simp [__smtx_typeof_set_member, native_ite, native_Teq, h1, h2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value
      (__smtx_model_eval_set_member (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
    SmtType.Bool
  rcases set_value_canonical (A := A)
      (by simpa [h2] using hpres2) with ⟨m, hm⟩
  have hmTy : __smtx_typeof_map_value m = SmtType.Map A SmtType.Bool := by
    apply set_map_value_typed (A := A)
    simpa [hm, h2] using hpres2
  rw [hm]
  simpa [__smtx_model_eval_set_member, __smtx_map_select] using
    map_lookup_typed (m := m) (A := A) (B := SmtType.Bool) (i := __smtx_model_eval M t1)
      hmTy
      (by simpa [h1] using hpres1)

/-- Shows that evaluating `set_subset` terms produces values of the expected type. -/
theorem typeof_value_model_eval_set_subset
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.set_subset t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.set_subset t1 t2)) =
      __smtx_typeof (SmtTerm.set_subset t1 t2) := by
  rcases set_binop_ret_args_of_non_none
      (op := SmtTerm.set_subset) (T := SmtType.Bool) (typeof_set_subset_eq t1 t2) ht with
    ⟨A, h1, h2⟩
  rw [show __smtx_typeof (SmtTerm.set_subset t1 t2) =
      SmtType.Bool by
    rw [typeof_set_subset_eq]
    simp [__smtx_typeof_sets_op_2_ret, native_ite, native_Teq, h1, h2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  simpa [__smtx_model_eval_set_subset] using
    typeof_value_model_eval_eq_value
      (__smtx_model_eval_set_inter (__smtx_model_eval M t1) (__smtx_model_eval M t2))
      (__smtx_model_eval M t1)

end Smtm
