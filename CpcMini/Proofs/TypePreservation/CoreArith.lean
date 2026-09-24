module

public import CpcMini.Proofs.TypePreservation.Helpers
import all CpcMini.Proofs.TypePreservation.Helpers

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
  rw [__smtx_typeof.eq_11]

/-- Rewrites the typing equation for `eq`. -/
theorem typeof_eq_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.eq t1 t2) =
      __smtx_typeof_eq (__smtx_typeof t1) (__smtx_typeof t2) := by
  rw [__smtx_typeof.eq_10]

/-- Rewrites the typing equation for `not`. -/
theorem typeof_not_eq (t : SmtTerm) :
    __smtx_typeof (SmtTerm.not t) =
      native_ite (native_Teq (__smtx_typeof t) SmtType.Bool) SmtType.Bool SmtType.None := by
  rw [__smtx_typeof.eq_6]

/-- Rewrites the typing equation for `or`. -/
theorem typeof_or_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.or t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) SmtType.Bool)
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.Bool) SmtType.Bool SmtType.None)
        SmtType.None := by
  rw [__smtx_typeof.eq_8]

/-- Rewrites the typing equation for `and`. -/
theorem typeof_and_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.and t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) SmtType.Bool)
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.Bool) SmtType.Bool SmtType.None)
        SmtType.None := by
  rw [__smtx_typeof.eq_7]

/-- Rewrites the typing equation for `imp`. -/
theorem typeof_imp_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.imp t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) SmtType.Bool)
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.Bool) SmtType.Bool SmtType.None)
        SmtType.None := by
  rw [__smtx_typeof.eq_9]

/-- Derives `bool_binop_args_bool` from `non_none`. -/
theorem bool_binop_args_bool_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2) =
        native_ite (native_Teq (__smtx_typeof t1) SmtType.Bool)
          (native_ite (native_Teq (__smtx_typeof t2) SmtType.Bool) SmtType.Bool SmtType.None)
          SmtType.None)
    (ht : term_has_non_none_type (op t1 t2)) :
    __smtx_typeof t1 = SmtType.Bool ∧ __smtx_typeof t2 = SmtType.Bool := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [hTy, native_ite, native_Teq, h1, h2] at ht
  simp

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
  rw [show __smtx_model_eval M (SmtTerm.ite c t1 t2) =
      __smtx_model_eval_ite (__smtx_model_eval M c) (__smtx_model_eval M t1) (__smtx_model_eval M t2) by
    simp [__smtx_model_eval]]
  rcases bool_value_canonical (by simpa [hc] using hpresc) with ⟨b, hb⟩
  rw [hb]
  cases b
  · simpa [__smtx_model_eval_ite, __smtx_typeof_value, h1, h2] using hpres2
  · simpa [__smtx_model_eval_ite, __smtx_typeof_value, h1, h2] using hpres1

/-- Derives `eq_term_typeof` from `non_none`. -/
theorem eq_term_typeof_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.eq t1 t2)) :
    __smtx_typeof (SmtTerm.eq t1 t2) = SmtType.Bool := by
  unfold term_has_non_none_type at ht
  rw [typeof_eq_eq] at ht ⊢
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
    rfl
  rw [show __smtx_typeof (SmtTerm.not t) = SmtType.Bool by
    rw [typeof_not_eq]
    simp [native_ite, native_Teq, hArg]]
  rw [show __smtx_model_eval M (SmtTerm.not t) =
      __smtx_model_eval_not (__smtx_model_eval M t) by
    simp [__smtx_model_eval]]
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
  have hTy :
      __smtx_typeof (SmtTerm.or t1 t2) =
        native_ite (native_Teq (__smtx_typeof t1) SmtType.Bool)
          (native_ite (native_Teq (__smtx_typeof t2) SmtType.Bool) SmtType.Bool SmtType.None)
          SmtType.None := typeof_or_eq t1 t2
  have hArgs := bool_binop_args_bool_of_non_none hTy ht
  rw [show __smtx_typeof (SmtTerm.or t1 t2) = SmtType.Bool by
    rw [typeof_or_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2]]
  rw [show __smtx_model_eval M (SmtTerm.or t1 t2) =
      __smtx_model_eval_or (__smtx_model_eval M t1) (__smtx_model_eval M t2) by
    simp [__smtx_model_eval]]
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
  have hTy :
      __smtx_typeof (SmtTerm.and t1 t2) =
        native_ite (native_Teq (__smtx_typeof t1) SmtType.Bool)
          (native_ite (native_Teq (__smtx_typeof t2) SmtType.Bool) SmtType.Bool SmtType.None)
          SmtType.None := typeof_and_eq t1 t2
  have hArgs := bool_binop_args_bool_of_non_none hTy ht
  rw [show __smtx_typeof (SmtTerm.and t1 t2) = SmtType.Bool by
    rw [typeof_and_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2]]
  rw [show __smtx_model_eval M (SmtTerm.and t1 t2) =
      __smtx_model_eval_and (__smtx_model_eval M t1) (__smtx_model_eval M t2) by
    simp [__smtx_model_eval]]
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
  have hTy :
      __smtx_typeof (SmtTerm.imp t1 t2) =
        native_ite (native_Teq (__smtx_typeof t1) SmtType.Bool)
          (native_ite (native_Teq (__smtx_typeof t2) SmtType.Bool) SmtType.Bool SmtType.None)
          SmtType.None := typeof_imp_eq t1 t2
  have hArgs := bool_binop_args_bool_of_non_none hTy ht
  rw [show __smtx_typeof (SmtTerm.imp t1 t2) = SmtType.Bool by
    rw [typeof_imp_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2]]
  rw [show __smtx_model_eval M (SmtTerm.imp t1 t2) =
      __smtx_model_eval_imp (__smtx_model_eval M t1) (__smtx_model_eval M t2) by
    simp [__smtx_model_eval]]
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
  rw [show __smtx_model_eval M (SmtTerm.eq t1 t2) =
      __smtx_model_eval_eq (__smtx_model_eval M t1) (__smtx_model_eval M t2) by
    simp [__smtx_model_eval]]
  simpa using typeof_value_model_eval_eq_value M (__smtx_model_eval M t1) (__smtx_model_eval M t2)

end Smtm
