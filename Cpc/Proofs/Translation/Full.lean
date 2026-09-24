module

public import Cpc.Proofs.Translation.Apply
import all Cpc.Proofs.TypePreservation.Common

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace TranslationProofs

attribute [local simp] Smtm.__smtx_type_wf_component
attribute [local simp] noNoneTy noNoneDecl noNoneDt noNoneDtc
attribute [local simp] native_and native_ite

/-!
Full translation-proof surface corresponding to the lightweight stub in
`Cpc.Proofs.Translation`.
-/

private theorem false_of_smtx_typeof_none_non_none_full {P : Prop}
    (h : __smtx_typeof SmtTerm.None ≠ SmtType.None) :
    P := by
  exact False.elim (h smtx_typeof_none)

private theorem false_of_typeof_apply_none_non_none_full {P : Prop}
    (x : SmtTerm)
    (h : __smtx_typeof (SmtTerm.Apply SmtTerm.None x) ≠ SmtType.None) :
    P := by
  exact False.elim (h (typeof_apply_none_eq x))

private theorem false_of_typeof_quaternary_none_non_none_full {P : Prop}
    (w z y x : SmtTerm)
    (h :
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None w) z) y) x) ≠
        SmtType.None) :
    P := by
  exact False.elim
    (h (typeof_apply_apply_apply_apply_none_head_eq w z y x))

private theorem eo_type_valid_of_valid_rec_top_full
    {T : Term}
    (h : eo_type_valid_rec [] T) :
    eo_type_valid T := by
  simpa [eo_type_valid, eo_type_valid_rec] using h

private theorem eo_type_valid_of_guard_wf_non_none_full
    {T U : Term}
    (h :
      __smtx_typeof_guard_wf (__eo_to_smt_type T) (__eo_to_smt_type U) ≠
        SmtType.None) :
    eo_type_valid T := by
  unfold __smtx_typeof_guard_wf at h
  have hWf : __smtx_type_wf (__eo_to_smt_type T) = true := by
    by_cases hWf : __smtx_type_wf (__eo_to_smt_type T) = true
    · exact hWf
    · exfalso
      simp [native_ite, hWf] at h
  exact eo_type_valid_of_smt_wf T hWf

private theorem eo_to_smt_type_eq_of_top_valid_full
    {T U : Term}
    (hValid : eo_type_valid T)
    (hEq : __eo_to_smt_type T = __eo_to_smt_type U) :
    T = U := by
  exact eo_to_smt_type_eq_of_valid hValid hEq

private theorem eo_type_valid_fun_codomain_full
    (T U : Term)
    (hValid : eo_type_valid (Term.Apply (Term.Apply Term.FunType T) U)) :
    eo_type_valid U := by
  unfold eo_type_valid at hValid ⊢
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp_all [__eo_to_smt_type, __smtx_typeof_guard, native_Teq]

private theorem eo_type_valid_dtc_codomain_full
    (T U : Term) (hValid : eo_type_valid (Term.DtcAppType T U)) :
    eo_type_valid U := by
  unfold eo_type_valid at hValid ⊢
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp_all [__eo_to_smt_type, __smtx_typeof_guard, native_Teq]

private theorem eo_type_valid_set_element_full
    (T : Term) (hValid : eo_type_valid (Term.Apply (Term.UOp UserOp.Set) T)) :
    eo_type_valid T := by
  unfold eo_type_valid at hValid ⊢
  cases hT : __eo_to_smt_type T <;>
    simp_all [__eo_to_smt_type, __smtx_typeof_guard, native_Teq]

private theorem eo_typeof_set_choose_arg_set_full {A : Term}
    (h : __eo_typeof_set_choose A ≠ Term.Stuck) :
    ∃ T, A = Term.Apply (Term.UOp UserOp.Set) T := by
  cases A <;> simp [__eo_typeof_set_choose] at h ⊢
  case Apply f T =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢

private theorem eo_type_valid_seq_element_full
    (T : Term) (hValid : eo_type_valid (Term.Apply (Term.UOp UserOp.Seq) T)) :
    eo_type_valid T := by
  unfold eo_type_valid at hValid ⊢
  cases hT : __eo_to_smt_type T <;>
    simp_all [__eo_to_smt_type, __smtx_typeof_guard, native_Teq]

private theorem eo_type_valid_map_components_full
    (T U : Term)
    (hValid : eo_type_valid (Term.Apply (Term.Apply (Term.UOp UserOp.Array) T) U)) :
    eo_type_valid T ∧ eo_type_valid U := by
  unfold eo_type_valid at hValid ⊢
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp_all [__eo_to_smt_type, __smtx_typeof_guard, native_Teq]

private theorem smtx_typeof_and_bool_or_none_full
    (s t : SmtTerm) :
    __smtx_typeof (SmtTerm.and s t) = SmtType.Bool ∨
      __smtx_typeof (SmtTerm.and s t) = SmtType.None := by
  cases hs : __smtx_typeof s <;>
    cases ht : __smtx_typeof t <;>
      (rw [typeof_and_eq]; simp [hs, ht, native_ite, native_Teq])

private theorem smtx_typeof_eo_to_smt_distinct_bool_or_none_full
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
            exact smtx_typeof_and_bool_or_none_full
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

private theorem smtx_typeof_eo_to_smt_distinct_of_non_none_full
    (xs : Term)
    (hNonNone : __smtx_typeof (__eo_to_smt_distinct xs) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt_distinct xs) = SmtType.Bool := by
  rcases smtx_typeof_eo_to_smt_distinct_bool_or_none_full xs with hBool | hNone
  · exact hBool
  · exact False.elim (hNonNone hNone)

private theorem native_Teq_none_false_of_non_none_full
    {T : SmtType}
    (h : T ≠ SmtType.None) :
    native_Teq T SmtType.None = false := by
  cases T <;> simp [native_Teq] at h ⊢

private theorem eo_typeof_typed_list_nil_of_non_stuck_full
    (T : Term)
    (hT : T ≠ Term.Stuck) :
    __eo_typeof__at__at_TypedList_nil Term.Type T =
      Term.Apply (Term.UOp UserOp._at__at_TypedList) T := by
  cases T <;> simp [__eo_typeof__at__at_TypedList_nil] at hT ⊢

private theorem eo_typeof_typed_list_cons_self_of_non_stuck_full
    (T : Term)
    (hT : T ≠ Term.Stuck) :
    __eo_typeof__at__at_TypedList_cons T
        (Term.Apply (Term.UOp UserOp._at__at_TypedList) T) =
      Term.Apply (Term.UOp UserOp._at__at_TypedList) T := by
  cases T <;> simp [__eo_typeof__at__at_TypedList_cons, __eo_requires,
    __eo_eq, native_ite, native_teq, native_not] at hT ⊢

private theorem eo_to_smt_typed_list_elem_type_of_non_none_full
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
                exact eo_typeof_typed_list_nil_of_non_stuck_full xs
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
                  rcases eo_to_smt_typed_list_elem_type_of_non_none_full root ih
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
                    exact eo_to_smt_type_eq_of_top_valid_full hHeadIH.2
                      (by rw [← hHeadIH.1, hHeadSmt])
                  refine ⟨T, ?_, ?_, hTValid⟩
                  · change
                      __eo_typeof__at__at_TypedList_cons (__eo_typeof t)
                          (__eo_typeof xs) =
                        Term.Apply (Term.UOp UserOp._at__at_TypedList) T
                    rw [hTsType, hHeadTypeEq]
                    exact eo_typeof_typed_list_cons_self_of_non_stuck_full T
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
                      simp
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

private theorem eo_type_valid_of_smt_type_eq_of_field_wf_full
    {T : Term} {A : SmtType}
    (hEq : __eo_to_smt_type T = A)
    (hA : smtx_type_field_wf_rec A native_reflist_nil) :
    eo_type_valid T := by
  exact eo_type_valid_of_valid_rec_top_full
    (eo_type_valid_of_smt_field_wf_rec native_reflist_nil (by
      simpa [hEq] using hA))

private theorem eo_type_valid_of_array_deq_diff_non_none_full
    (x1 x2 : Term)
    (hEq :
      __smtx_typeof (__eo_to_smt (Term._at_array_deq_diff x1 x2)) =
        __eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2)))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term._at_array_deq_diff x1 x2)) ≠
        SmtType.None) :
    eo_type_valid (__eo_typeof (Term._at_array_deq_diff x1 x2)) := by
  change
    __smtx_typeof
        (__eo_to_smt_array_deq_diff (__eo_to_smt x1)
          (__smtx_typeof (__eo_to_smt x1)) (__eo_to_smt x2)
          (__smtx_typeof (__eo_to_smt x2))) ≠
      SmtType.None at hNonNone
  cases hx1Smt : __smtx_typeof (__eo_to_smt x1) <;>
    cases hx2Smt : __smtx_typeof (__eo_to_smt x2) <;>
    simp [__eo_to_smt_array_deq_diff, hx1Smt, hx2Smt, smtx_typeof_none]
      at hNonNone
  case Map.Map A B A' B' =>
    have hMapNN :
        term_has_non_none_type (SmtTerm.map_diff (__eo_to_smt x1) (__eo_to_smt x2)) := by
      unfold term_has_non_none_type
      exact hNonNone
    rcases map_diff_args_of_non_none hMapNN with
      ⟨A, B, hx1Ty, _hx2Ty, hDiffTy⟩ |
      ⟨A, hx1Ty, _hx2Ty, hDiffTy⟩
    · have hAField :
          smtx_type_field_wf_rec A native_reflist_nil :=
        smtx_type_field_wf_rec_of_type_wf_rec
          (smt_map_components_wf_rec_of_non_none_type
            (__eo_to_smt x1) A B hx1Ty).1
      have hEoA :
          __eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2)) = A := by
        rw [← hEq]
        change
          __smtx_typeof
              (__eo_to_smt_array_deq_diff (__eo_to_smt x1)
                (__smtx_typeof (__eo_to_smt x1)) (__eo_to_smt x2)
                (__smtx_typeof (__eo_to_smt x2))) =
            A
        simpa [__eo_to_smt_array_deq_diff, hx1Smt, hx2Smt] using hDiffTy
      exact eo_type_valid_of_smt_type_eq_of_field_wf_full hEoA hAField
    · have hAField :
          smtx_type_field_wf_rec A native_reflist_nil :=
        smtx_type_field_wf_rec_of_type_wf_rec
          (smt_set_component_wf_rec_of_non_none_type
            (__eo_to_smt x1) A hx1Ty)
      have hEoA :
          __eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2)) = A := by
        rw [← hEq]
        change
          __smtx_typeof
              (__eo_to_smt_array_deq_diff (__eo_to_smt x1)
                (__smtx_typeof (__eo_to_smt x1)) (__eo_to_smt x2)
                (__smtx_typeof (__eo_to_smt x2))) =
            A
        simpa [__eo_to_smt_array_deq_diff, hx1Smt, hx2Smt] using hDiffTy
      exact eo_type_valid_of_smt_type_eq_of_field_wf_full hEoA hAField

private theorem eo_type_valid_of_sets_deq_diff_non_none_full
    (x1 x2 : Term)
    (hEq :
      __smtx_typeof (__eo_to_smt (Term._at_sets_deq_diff x1 x2)) =
        __eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2)))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term._at_sets_deq_diff x1 x2)) ≠
        SmtType.None) :
    eo_type_valid (__eo_typeof (Term._at_sets_deq_diff x1 x2)) := by
  change
    __smtx_typeof
        (__eo_to_smt_sets_deq_diff (__eo_to_smt x1)
          (__smtx_typeof (__eo_to_smt x1)) (__eo_to_smt x2)
          (__smtx_typeof (__eo_to_smt x2))) ≠
      SmtType.None at hNonNone
  cases hx1Smt : __smtx_typeof (__eo_to_smt x1) <;>
    cases hx2Smt : __smtx_typeof (__eo_to_smt x2) <;>
    simp [__eo_to_smt_sets_deq_diff, hx1Smt, hx2Smt, smtx_typeof_none]
      at hNonNone
  case Set.Set A A' =>
    have hMapNN :
        term_has_non_none_type (SmtTerm.map_diff (__eo_to_smt x1) (__eo_to_smt x2)) := by
      unfold term_has_non_none_type
      exact hNonNone
    rcases map_diff_args_of_non_none hMapNN with
      ⟨A, B, hx1Ty, _hx2Ty, hDiffTy⟩ |
      ⟨A, hx1Ty, _hx2Ty, hDiffTy⟩
    · have hAField :
          smtx_type_field_wf_rec A native_reflist_nil :=
        smtx_type_field_wf_rec_of_type_wf_rec
          (smt_map_components_wf_rec_of_non_none_type
            (__eo_to_smt x1) A B hx1Ty).1
      have hEoA :
          __eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2)) = A := by
        rw [← hEq]
        change
          __smtx_typeof
              (__eo_to_smt_sets_deq_diff (__eo_to_smt x1)
                (__smtx_typeof (__eo_to_smt x1)) (__eo_to_smt x2)
                (__smtx_typeof (__eo_to_smt x2))) =
            A
        simpa [__eo_to_smt_sets_deq_diff, hx1Smt, hx2Smt] using hDiffTy
      exact eo_type_valid_of_smt_type_eq_of_field_wf_full hEoA hAField
    · have hAField :
          smtx_type_field_wf_rec A native_reflist_nil :=
        smtx_type_field_wf_rec_of_type_wf_rec
          (smt_set_component_wf_rec_of_non_none_type
            (__eo_to_smt x1) A hx1Ty)
      have hEoA :
          __eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2)) = A := by
        rw [← hEq]
        change
          __smtx_typeof
              (__eo_to_smt_sets_deq_diff (__eo_to_smt x1)
                (__smtx_typeof (__eo_to_smt x1)) (__eo_to_smt x2)
                (__smtx_typeof (__eo_to_smt x2))) =
            A
        simpa [__eo_to_smt_sets_deq_diff, hx1Smt, hx2Smt] using hDiffTy
      exact eo_type_valid_of_smt_type_eq_of_field_wf_full hEoA hAField

private theorem eo_typeof_tuple_select_of_non_stuck_full
    (i T : Term)
    (hi : i ≠ Term.Stuck)
    (hT : T ≠ Term.Stuck) :
    __eo_typeof_tuple_select (Term.UOp UserOp.Int) i T =
      __eo_list_nth (Term.UOp UserOp.Tuple) T i := by
  cases i <;> cases T <;> simp [__eo_typeof_tuple_select] at hi hT ⊢

private theorem eo_typeof_at_witness_string_length_of_non_stuck_full
    (T : Term)
    (hT : T ≠ Term.Stuck) :
    __eo_typeof__at_witness_string_length Term.Type T
      (Term.UOp UserOp.Int) (Term.UOp UserOp.Int) = T := by
  cases T <;> simp [__eo_typeof__at_witness_string_length] at hT ⊢

private theorem eo_type_valid_of_update_eq_dtcapp_full
    {z y x A B : Term}
    (hYValid : eo_type_valid (__eo_typeof y))
    (hTy :
      __eo_typeof_update (__eo_typeof z) (__eo_typeof y) (__eo_typeof x) =
        Term.DtcAppType A B) :
    eo_type_valid (Term.DtcAppType A B) := by
  unfold __eo_typeof_update at hTy
  repeat (first | split at hTy)
  all_goals
    first
      | cases hTy
      | rw [← hTy]
        exact hYValid

private theorem eo_type_valid_of_requires_eq_dtcapp_pre_full
    {T V U A B : Term}
    (hU : eo_type_valid U)
    (hReq : __eo_requires T V U = Term.DtcAppType A B) :
    eo_type_valid (Term.DtcAppType A B) := by
  unfold __eo_requires at hReq
  cases hEq : native_teq T V <;> simp [native_ite, hEq] at hReq
  cases hStuck : native_teq T Term.Stuck <;>
    simp [hStuck, native_not] at hReq
  all_goals first
    | rw [← hReq]; exact hU
    | exact hU
    | cases hReq

private theorem eo_type_valid_of_tuple_update_eq_dtcapp_full
    {z y x A B : Term}
    (hYValid : eo_type_valid (__eo_typeof y))
    (hTy :
      __eo_typeof_tuple_update (__eo_typeof z) z (__eo_typeof y) (__eo_typeof x) =
        Term.DtcAppType A B) :
    eo_type_valid (Term.DtcAppType A B) := by
  unfold __eo_typeof_tuple_update at hTy
  repeat (first | split at hTy)
  all_goals
    first
      | cases hTy
      | exact eo_type_valid_of_requires_eq_dtcapp_pre_full hYValid hTy

private theorem eo_type_valid_of_ite_eq_dtcapp_full
    {z y x A B : Term}
    (hYValid : eo_type_valid (__eo_typeof y))
    (hTy :
      __eo_typeof_ite (__eo_typeof z) (__eo_typeof y) (__eo_typeof x) =
        Term.DtcAppType A B) :
    eo_type_valid (Term.DtcAppType A B) := by
  unfold __eo_typeof_ite at hTy
  repeat (first | split at hTy)
  all_goals
    first
      | cases hTy
      | exact eo_type_valid_of_requires_eq_dtcapp_pre_full hYValid hTy

private theorem eo_type_valid_of_bvite_eq_dtcapp_full
    {z y x A B : Term}
    (hYValid : eo_type_valid (__eo_typeof y))
    (hTy :
      __eo_typeof_bvite (__eo_typeof z) (__eo_typeof y) (__eo_typeof x) =
        Term.DtcAppType A B) :
    eo_type_valid (Term.DtcAppType A B) := by
  unfold __eo_typeof_bvite at hTy
  repeat (first | split at hTy)
  all_goals
    first
      | cases hTy
      | exact eo_type_valid_of_requires_eq_dtcapp_pre_full hYValid hTy

private theorem false_of_requires_eq_dtcapp_of_payload_ne_full
    {T V U A B : Term}
    (hU : U ≠ Term.DtcAppType A B)
    (hReq : __eo_requires T V U = Term.DtcAppType A B) :
    False := by
  unfold __eo_requires at hReq
  cases hEq : native_teq T V <;> simp [native_ite, hEq] at hReq
  cases hStuck : native_teq T Term.Stuck <;>
    simp [hStuck, native_not] at hReq
  all_goals first
    | exact hU hReq
    | cases hReq

private theorem false_of_typeof_store_eq_dtcapp_full
    {z y x A B : Term}
    (hTy :
      __eo_typeof_store (__eo_typeof z) (__eo_typeof y) (__eo_typeof x) =
        Term.DtcAppType A B) :
    False := by
  unfold __eo_typeof_store at hTy
  repeat (first | split at hTy)
  all_goals
    first
      | cases hTy
      | exact false_of_requires_eq_dtcapp_of_payload_ne_full
          (by intro h; cases h) hTy

private theorem false_of_typeof_str_substr_eq_dtcapp_full
    {z y x A B : Term}
    (hTy :
      __eo_typeof_str_substr (__eo_typeof z) (__eo_typeof y) (__eo_typeof x) =
        Term.DtcAppType A B) :
    False := by
  unfold __eo_typeof_str_substr at hTy
  repeat (first | split at hTy)
  all_goals cases hTy

private theorem false_of_typeof_str_replace_eq_dtcapp_full
    {z y x A B : Term}
    (hTy :
      __eo_typeof_str_replace (__eo_typeof z) (__eo_typeof y) (__eo_typeof x) =
        Term.DtcAppType A B) :
    False := by
  unfold __eo_typeof_str_replace at hTy
  repeat (first | split at hTy)
  all_goals
    first
      | cases hTy
      | exact false_of_requires_eq_dtcapp_of_payload_ne_full
          (by intro h; cases h) hTy

private theorem false_of_typeof_str_indexof_eq_dtcapp_full
    {z y x A B : Term}
    (hTy :
      __eo_typeof_str_indexof (__eo_typeof z) (__eo_typeof y) (__eo_typeof x) =
        Term.DtcAppType A B) :
    False := by
  unfold __eo_typeof_str_indexof at hTy
  repeat (first | split at hTy)
  all_goals
    first
      | cases hTy
      | exact false_of_requires_eq_dtcapp_of_payload_ne_full
          (by intro h; cases h) hTy

private theorem false_of_typeof_str_update_eq_dtcapp_full
    {z y x A B : Term}
    (hTy :
      __eo_typeof_str_update (__eo_typeof z) (__eo_typeof y) (__eo_typeof x) =
        Term.DtcAppType A B) :
    False := by
  unfold __eo_typeof_str_update at hTy
  repeat (first | split at hTy)
  all_goals
    first
      | cases hTy
      | exact false_of_requires_eq_dtcapp_of_payload_ne_full
          (by intro h; cases h) hTy

private theorem false_of_typeof_str_replace_re_eq_dtcapp_full
    {z y x A B : Term}
    (hTy :
      __eo_typeof_str_replace_re (__eo_typeof z) (__eo_typeof y) (__eo_typeof x) =
        Term.DtcAppType A B) :
    False := by
  unfold __eo_typeof_str_replace_re at hTy
  repeat (first | split at hTy)
  all_goals cases hTy

private theorem false_of_typeof_str_indexof_re_eq_dtcapp_full
    {z y x A B : Term}
    (hTy :
      __eo_typeof_str_indexof_re (__eo_typeof z) (__eo_typeof y) (__eo_typeof x) =
        Term.DtcAppType A B) :
    False := by
  unfold __eo_typeof_str_indexof_re at hTy
  repeat (first | split at hTy)
  all_goals cases hTy

private theorem false_of_typeof_strings_num_occur_re_eq_dtcapp_full
    {y x A B : Term}
    (hTy :
      __eo_typeof__at_strings_num_occur_re (__eo_typeof y) (__eo_typeof x) =
        Term.DtcAppType A B) :
    False := by
  unfold __eo_typeof__at_strings_num_occur_re at hTy
  repeat (first | split at hTy)
  all_goals cases hTy

private theorem false_of_typeof_strings_replace_all_result_eq_dtcapp_full
    {w z y x A B : Term}
    (hTy :
      __eo_typeof__at_strings_replace_all_result
          (__eo_typeof w) (__eo_typeof z) (__eo_typeof y) (__eo_typeof x) =
        Term.DtcAppType A B) :
    False := by
  unfold __eo_typeof__at_strings_replace_all_result at hTy
  repeat (first | split at hTy)
  all_goals
    first
      | cases hTy
      | exact false_of_requires_eq_dtcapp_of_payload_ne_full
          (by intro h; cases h) hTy

private theorem false_of_typeof_strings_replace_re_all_result_eq_dtcapp_full
    {w z y x A B : Term}
    (hTy :
      __eo_typeof__at_strings_replace_re_all_result
          (__eo_typeof w) (__eo_typeof z) (__eo_typeof y) (__eo_typeof x) =
        Term.DtcAppType A B) :
    False := by
  unfold __eo_typeof__at_strings_replace_re_all_result at hTy
  repeat (first | split at hTy)
  all_goals cases hTy

private theorem eo_type_valid_of_requires_eq_dtcapp_full
    {T V U A B : Term}
    (hU : eo_type_valid U)
    (hReq : __eo_requires T V U = Term.DtcAppType A B) :
    eo_type_valid (Term.DtcAppType A B) := by
  unfold __eo_requires at hReq
  cases hEq : native_teq T V <;> simp [native_ite, hEq] at hReq
  cases hStuck : native_teq T Term.Stuck <;>
    simp [hStuck, native_not] at hReq
  all_goals first
    | rw [← hReq]; exact hU
    | exact hU
    | cases hReq

private theorem eo_type_valid_of_typeof_apply_eq_dtcapp_full
    {F X A B : Term}
    (hF : eo_type_valid F)
    (hTy : __eo_typeof_apply F X = Term.DtcAppType A B) :
    eo_type_valid (Term.DtcAppType A B) := by
  have hFun :
      ∀ T U, F = Term.Apply (Term.Apply Term.FunType T) U ->
        eo_type_valid U := by
    intro T U hFU
    subst F
    exact eo_type_valid_fun_codomain_full T U hF
  have hDtc :
      ∀ T U, F = Term.DtcAppType T U -> eo_type_valid U := by
    intro T U hFU
    subst F
    exact eo_type_valid_dtc_codomain_full T U hF
  clear hF
  cases X <;> try cases hTy
  all_goals
    cases F <;> try cases hTy
    case Apply f U =>
      cases f <;> try cases hTy
      case Apply g T =>
        cases g <;> try cases hTy
        case FunType =>
          exact eo_type_valid_of_requires_eq_dtcapp_full
            (hFun T U rfl) hTy
    case DtcAppType T U =>
      exact eo_type_valid_of_requires_eq_dtcapp_full
        (hDtc T U rfl) hTy

private theorem eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
    {F X A B : Term}
    (hFun :
      ∀ T U, F = Term.Apply (Term.Apply Term.FunType T) U ->
        eo_type_valid U)
    (hDtc :
      ∀ T U, F = Term.DtcAppType T U -> eo_type_valid U)
    (hTy : __eo_typeof_apply F X = Term.DtcAppType A B) :
    eo_type_valid (Term.DtcAppType A B) := by
  cases X <;> try cases hTy
  all_goals
    cases F <;> try cases hTy
    case Apply f U =>
      cases f <;> try cases hTy
      case Apply g T =>
        cases g <;> try cases hTy
        case FunType =>
          exact eo_type_valid_of_requires_eq_dtcapp_full
            (hFun T U rfl) hTy
    case DtcAppType T U =>
      exact eo_type_valid_of_requires_eq_dtcapp_full
        (hDtc T U rfl) hTy

private theorem eo_type_valid_of_requires_eq_dtcapp_cases_full
    {T V U A B : Term}
    (hU : U = Term.DtcAppType A B -> eo_type_valid U)
    (hReq : __eo_requires T V U = Term.DtcAppType A B) :
    eo_type_valid (Term.DtcAppType A B) := by
  unfold __eo_requires at hReq
  cases hEq : native_teq T V <;> simp [native_ite, hEq] at hReq
  cases hStuck : native_teq T Term.Stuck <;>
    simp [hStuck, native_not] at hReq
  all_goals first
    | have hValid := hU hReq
      simpa [hReq] using hValid
    | cases hReq

private theorem eo_type_valid_of_typeof_apply_eq_dtcapp_cond_cases_full
    {F X A B : Term}
    (hFun :
      ∀ T U, F = Term.Apply (Term.Apply Term.FunType T) U ->
        U = Term.DtcAppType A B -> eo_type_valid U)
    (hDtc :
      ∀ T U, F = Term.DtcAppType T U ->
        U = Term.DtcAppType A B -> eo_type_valid U)
    (hTy : __eo_typeof_apply F X = Term.DtcAppType A B) :
    eo_type_valid (Term.DtcAppType A B) := by
  cases X <;> try cases hTy
  all_goals
    cases F <;> try cases hTy
    case Apply f U =>
      cases f <;> try cases hTy
      case Apply g T =>
        cases g <;> try cases hTy
        case FunType =>
          exact eo_type_valid_of_requires_eq_dtcapp_cases_full
            (fun hU => hFun T U rfl hU) hTy
    case DtcAppType T U =>
      exact eo_type_valid_of_requires_eq_dtcapp_cases_full
        (fun hU => hDtc T U rfl hU) hTy

private theorem false_of_typeof_BitVec_eq_dtcapp_full
    {x A B : Term}
    (hTy : __eo_typeof_BitVec (__eo_typeof x) = Term.DtcAppType A B) :
    False := by
  cases hx : __eo_typeof x <;> simp [__eo_typeof_BitVec, hx] at hTy
  case UOp op =>
    cases op <;> simp at hTy

private theorem false_of_typeof_typed_list_nil_eq_dtcapp_full
    {x A B : Term}
    (hTy :
      __eo_typeof__at__at_TypedList_nil (__eo_typeof x) x =
        Term.DtcAppType A B) :
    False := by
  cases hx : __eo_typeof x <;> cases x <;>
    simp [__eo_typeof__at__at_TypedList_nil, hx] at hTy

private theorem false_of_typeof_distinct_eq_dtcapp_full
    {x A B : Term}
    (hTy : __eo_typeof_distinct (__eo_typeof x) = Term.DtcAppType A B) :
  False := by
  cases hx : __eo_typeof x <;> simp [__eo_typeof_distinct, hx] at hTy
  case Apply f y =>
    cases f <;> try cases hTy
    case UOp op =>
      cases op <;> try cases hTy
      all_goals
        cases y <;> try cases hTy
        case UOp op' =>
          cases op' <;> cases hTy

private theorem false_of_typeof_to_real_eq_dtcapp_full
    {x A B : Term}
    (hTy : __eo_typeof_to_real (__eo_typeof x) = Term.DtcAppType A B) :
  False := by
  cases hx : __eo_typeof x <;>
    simp [__eo_typeof_to_real, hx] at hTy
  case UOp op =>
    cases op <;> simp at hTy

private theorem false_of_typeof_to_int_eq_dtcapp_full
    {x A B : Term}
    (hTy : __eo_typeof_to_int (__eo_typeof x) = Term.DtcAppType A B) :
    False := by
  cases hx : __eo_typeof x <;> simp [__eo_typeof_to_int, hx] at hTy
  case UOp op =>
    cases op <;> simp at hTy

private theorem false_of_typeof_is_int_eq_dtcapp_full
    {x A B : Term}
    (hTy : __eo_typeof_is_int (__eo_typeof x) = Term.DtcAppType A B) :
    False := by
  cases hx : __eo_typeof x <;> simp [__eo_typeof_is_int, hx] at hTy
  case UOp op =>
    cases op <;> simp at hTy

private theorem false_of_typeof_abs_eq_dtcapp_full
    {x A B : Term}
    (hTy : __eo_typeof_abs (__eo_typeof x) = Term.DtcAppType A B) :
  False := by
  cases hx : __eo_typeof x <;>
    simp [__eo_typeof_abs, __is_arith_type, __eo_requires,
      native_ite, native_teq, native_not, hx] at hTy
  case UOp op =>
    cases op <;> simp at hTy

private theorem false_of_typeof_plus_eq_dtcapp_full
    {Y X A B : Term}
    (hTy : __eo_typeof_plus Y X = Term.DtcAppType A B) :
    False := by
  cases Y <;> cases X <;>
    simp [__eo_typeof_plus, __is_arith_type, __eo_requires, __eo_eq,
      native_ite, native_teq, native_not] at hTy
  all_goals
    try cases ‹UserOp›
  all_goals
    try cases ‹UserOp›
  all_goals
    try cases ‹UserOp›
  all_goals
    try simp at hTy
  all_goals
    try cases hTy

private theorem false_of_typeof_lt_eq_dtcapp_full
    {Y X A B : Term}
    (hTy : __eo_typeof_lt Y X = Term.DtcAppType A B) :
    False := by
  cases Y <;> cases X <;>
    simp [__eo_typeof_lt, __is_arith_type, __eo_requires, __eo_eq,
      native_ite, native_teq, native_not] at hTy
  all_goals
    try cases ‹UserOp›
  all_goals
    try cases ‹UserOp›
  all_goals
    try simp at hTy
  all_goals
    try cases hTy

private theorem false_of_typeof_set_member_eq_dtcapp_full
    {Y X A B : Term}
    (hTy : __eo_typeof_set_member Y X = Term.DtcAppType A B) :
    False := by
  unfold __eo_typeof_set_member at hTy
  repeat (first | split at hTy)
  all_goals first
    | cases hTy
    | exact false_of_requires_eq_dtcapp_of_payload_ne_full
        (by intro h; cases h) hTy

private theorem false_of_typeof_qdiv_eq_dtcapp_full
    {Y X A B : Term}
    (hTy : __eo_typeof_qdiv Y X = Term.DtcAppType A B) :
    False := by
  cases Y <;> cases X <;>
    simp [__eo_typeof_qdiv, __is_arith_type, __eo_requires, __eo_eq,
      native_ite, native_teq, native_not] at hTy
  all_goals
    try cases ‹UserOp›
  all_goals
    try cases ‹UserOp›
  all_goals
    try simp at hTy
  all_goals
    try cases hTy

private theorem false_of_typeof_int_pow2_eq_dtcapp_full
    {x A B : Term}
    (hTy : __eo_typeof_int_pow2 (__eo_typeof x) = Term.DtcAppType A B) :
    False := by
  cases hx : __eo_typeof x <;> simp [__eo_typeof_int_pow2, hx] at hTy
  case UOp op =>
    cases op <;> simp at hTy

private theorem false_of_typeof_int_ispow2_eq_dtcapp_full
    {x A B : Term}
    (hTy : __eo_typeof_int_ispow2 (__eo_typeof x) = Term.DtcAppType A B) :
    False := by
  cases hx : __eo_typeof x <;> simp [__eo_typeof_int_ispow2, hx] at hTy
  case UOp op =>
    cases op <;> simp at hTy

private theorem false_of_typeof_at_bvsize_eq_dtcapp_full
    {x A B : Term}
    (hTy : __eo_typeof__at_bvsize (__eo_typeof x) = Term.DtcAppType A B) :
    False := by
  cases hx : __eo_typeof x <;> simp [__eo_typeof__at_bvsize, hx] at hTy
  case Apply f y =>
    cases f <;> try cases hTy
    case UOp op =>
      cases op <;> try cases hTy
      all_goals
        cases y <;> try cases hTy
        case UOp op' =>
          cases op' <;> cases hTy

private theorem false_of_typeof_bvnot_eq_dtcapp_full
    {x A B : Term}
    (hTy : __eo_typeof_bvnot (__eo_typeof x) = Term.DtcAppType A B) :
  False := by
  cases hx : __eo_typeof x <;> simp [__eo_typeof_bvnot, hx] at hTy
  case Apply f y =>
    cases f <;> try cases hTy
    case UOp op =>
      cases op <;> try cases hTy
      all_goals
        cases y <;> try cases hTy
        case UOp op' =>
          cases op' <;> cases hTy

private theorem false_of_typeof_bvnego_eq_dtcapp_full
    {x A B : Term}
    (hTy : __eo_typeof_bvnego (__eo_typeof x) = Term.DtcAppType A B) :
  False := by
  cases hx : __eo_typeof x <;> simp [__eo_typeof_bvnego, hx] at hTy
  case Apply f y =>
    cases f <;> try cases hTy
    case UOp op =>
      cases op <;> try cases hTy
      all_goals
        cases y <;> try cases hTy
        case UOp op' =>
          cases op' <;> cases hTy

private theorem false_of_typeof_bvredand_eq_dtcapp_full
    {x A B : Term}
    (hTy : __eo_typeof_bvredand (__eo_typeof x) = Term.DtcAppType A B) :
  False := by
  cases hx : __eo_typeof x <;> simp [__eo_typeof_bvredand, hx] at hTy
  case Apply f y =>
    cases f <;> try cases hTy
    case UOp op =>
      cases op <;> try cases hTy
      all_goals
        cases y <;> try cases hTy
        case UOp op' =>
          cases op' <;> cases hTy

private theorem false_of_typeof_str_len_eq_dtcapp_full
    {x A B : Term}
    (hTy : __eo_typeof_str_len (__eo_typeof x) = Term.DtcAppType A B) :
  False := by
  cases hx : __eo_typeof x <;> simp [__eo_typeof_str_len, hx] at hTy
  case Apply f y =>
    cases f <;> try cases hTy
    case UOp op =>
      cases op <;> try cases hTy
      all_goals
        cases y <;> try cases hTy
        case UOp op' =>
          cases op' <;> cases hTy

private theorem false_of_typeof_str_rev_eq_dtcapp_full
    {x A B : Term}
    (hTy : __eo_typeof_str_rev (__eo_typeof x) = Term.DtcAppType A B) :
  False := by
  cases hx : __eo_typeof x <;> simp [__eo_typeof_str_rev, hx] at hTy
  case Apply f y =>
    cases f <;> try cases hTy
    case UOp op =>
      cases op <;> try cases hTy
      all_goals
        cases y <;> try cases hTy
        case UOp op' =>
          cases op' <;> cases hTy

private theorem false_of_typeof_str_to_lower_eq_dtcapp_full
    {x A B : Term}
    (hTy : __eo_typeof_str_to_lower (__eo_typeof x) = Term.DtcAppType A B) :
  False := by
  cases hx : __eo_typeof x <;> simp [__eo_typeof_str_to_lower, hx] at hTy
  case Apply f y =>
    cases f <;> try cases hTy
    case UOp op =>
      cases op <;> try cases hTy
      all_goals
        cases y <;> try cases hTy
        case UOp op' =>
          cases op' <;> cases hTy

private theorem false_of_typeof_str_to_code_eq_dtcapp_full
    {x A B : Term}
    (hTy : __eo_typeof_str_to_code (__eo_typeof x) = Term.DtcAppType A B) :
  False := by
  cases hx : __eo_typeof x <;> simp [__eo_typeof_str_to_code, hx] at hTy
  case Apply f y =>
    cases f <;> try cases hTy
    case UOp op =>
      cases op <;> try cases hTy
      all_goals
        cases y <;> try cases hTy
        case UOp op' =>
          cases op' <;> cases hTy

private theorem false_of_typeof_str_from_code_eq_dtcapp_full
    {x A B : Term}
    (hTy : __eo_typeof_str_from_code (__eo_typeof x) = Term.DtcAppType A B) :
    False := by
  cases hx : __eo_typeof x <;> simp [__eo_typeof_str_from_code, hx] at hTy
  case UOp op =>
    cases op <;> simp at hTy

private theorem false_of_typeof_str_is_digit_eq_dtcapp_full
    {x A B : Term}
    (hTy : __eo_typeof_str_is_digit (__eo_typeof x) = Term.DtcAppType A B) :
  False := by
  cases hx : __eo_typeof x <;> simp [__eo_typeof_str_is_digit, hx] at hTy
  case Apply f y =>
    cases f <;> try cases hTy
    case UOp op =>
      cases op <;> try cases hTy
      all_goals
        cases y <;> try cases hTy
        case UOp op' =>
          cases op' <;> cases hTy

private theorem false_of_typeof_str_to_re_eq_dtcapp_full
    {x A B : Term}
    (hTy : __eo_typeof_str_to_re (__eo_typeof x) = Term.DtcAppType A B) :
  False := by
  cases hx : __eo_typeof x <;> simp [__eo_typeof_str_to_re, hx] at hTy
  case Apply f y =>
    cases f <;> try cases hTy
    case UOp op =>
      cases op <;> try cases hTy
      all_goals
        cases y <;> try cases hTy
        case UOp op' =>
          cases op' <;> cases hTy

private theorem false_of_typeof_re_mult_eq_dtcapp_full
    {x A B : Term}
    (hTy : __eo_typeof_re_mult (__eo_typeof x) = Term.DtcAppType A B) :
    False := by
  cases hx : __eo_typeof x <;> simp [__eo_typeof_re_mult, hx] at hTy
  case UOp op =>
    cases op <;> simp at hTy

private theorem false_of_typeof_seq_unit_eq_dtcapp_full
    {x A B : Term}
    (hTy : __eo_typeof_seq_unit (__eo_typeof x) = Term.DtcAppType A B) :
    False := by
  cases hx : __eo_typeof x <;> simp [__eo_typeof_seq_unit, hx] at hTy

private theorem false_of_typeof_set_singleton_eq_dtcapp_full
    {x A B : Term}
    (hTy : __eo_typeof_set_singleton (__eo_typeof x) = Term.DtcAppType A B) :
    False := by
  cases hx : __eo_typeof x <;> simp [__eo_typeof_set_singleton, hx] at hTy

private theorem false_of_typeof_set_is_empty_eq_dtcapp_full
    {x A B : Term}
    (hTy : __eo_typeof_set_is_empty (__eo_typeof x) = Term.DtcAppType A B) :
    False := by
  cases hx : __eo_typeof x <;> simp [__eo_typeof_set_is_empty, hx] at hTy
  case Apply f y =>
    cases f <;> try cases hTy
    case UOp op =>
      cases op <;> cases hTy

private theorem false_of_typeof_div_by_zero_eq_dtcapp_full
    {x A B : Term}
    (hTy : __eo_typeof__at_div_by_zero (__eo_typeof x) = Term.DtcAppType A B) :
    False := by
  cases hx : __eo_typeof x <;> simp [__eo_typeof__at_div_by_zero, hx] at hTy
  case UOp op =>
    cases op <;> simp at hTy

private theorem eo_mk_apply_ne_dtcapp_full
    (f x A B : Term) :
    __eo_mk_apply f x ≠ Term.DtcAppType A B := by
  intro h
  cases f <;> cases x <;> simp [__eo_mk_apply] at h

private theorem eo_apply_ne_dtcapp_full
    (f x A B : Term) :
    Term.Apply f x ≠ Term.DtcAppType A B := by
  intro h
  cases h

private theorem false_of_typeof_re_loop_eq_dtcapp_full
    {y z x A B : Term}
    (hTy :
      __eo_typeof_re_loop (__eo_typeof y) y (__eo_typeof z) z (__eo_typeof x) =
        Term.DtcAppType A B) :
    False := by
  unfold __eo_typeof_re_loop at hTy
  repeat (first | split at hTy)
  all_goals
    first
      | cases hTy
      | exact false_of_requires_eq_dtcapp_of_payload_ne_full
          (fun h =>
            false_of_requires_eq_dtcapp_of_payload_ne_full (by intro hh; cases hh) h)
          hTy

private theorem false_of_typeof_repeat_eq_dtcapp_full
    {y x A B : Term}
    (hTy :
      __eo_typeof_repeat (__eo_typeof y) y (__eo_typeof x) =
        Term.DtcAppType A B) :
    False := by
  unfold __eo_typeof_repeat at hTy
  repeat (first | split at hTy)
  all_goals
    first
      | cases hTy
      | exact false_of_requires_eq_dtcapp_of_payload_ne_full
          (eo_mk_apply_ne_dtcapp_full _ _ A B)
          hTy

private theorem false_of_typeof_zero_extend_eq_dtcapp_full
    {y x A B : Term}
    (hTy :
      __eo_typeof_zero_extend (__eo_typeof y) y (__eo_typeof x) =
        Term.DtcAppType A B) :
    False := by
  unfold __eo_typeof_zero_extend at hTy
  repeat (first | split at hTy)
  all_goals
    first
      | cases hTy
      | exact false_of_requires_eq_dtcapp_of_payload_ne_full
          (eo_mk_apply_ne_dtcapp_full _ _ A B)
          hTy

private theorem false_of_typeof_rotate_left_eq_dtcapp_full
    {y x A B : Term}
    (hTy :
      __eo_typeof_rotate_left (__eo_typeof y) y (__eo_typeof x) =
        Term.DtcAppType A B) :
    False := by
  unfold __eo_typeof_rotate_left at hTy
  repeat (first | split at hTy)
  all_goals
    first
      | cases hTy
      | exact false_of_requires_eq_dtcapp_of_payload_ne_full
          (eo_apply_ne_dtcapp_full _ _ A B)
          hTy

private theorem false_of_typeof_at_bit2_eq_dtcapp_full
    {y x A B : Term}
    (hTy :
      __eo_typeof__at_bit (__eo_typeof y) (__eo_typeof x) =
        Term.DtcAppType A B) :
    False := by
  cases hy : __eo_typeof y <;> simp [__eo_typeof__at_bit, hy] at hTy
  case UOp op =>
    cases op <;> try cases hTy
    case Int =>
      cases hx : __eo_typeof x <;> simp [hx] at hTy
      case Apply f m =>
        cases f <;> try cases hTy
        case UOp op' =>
          cases op' <;> cases hTy

private theorem false_of_typeof_re_exp_eq_dtcapp_full
    {y x A B : Term}
    (hTy :
      __eo_typeof_re_exp (__eo_typeof y) y (__eo_typeof x) =
        Term.DtcAppType A B) :
    False := by
  unfold __eo_typeof_re_exp at hTy
  repeat (first | split at hTy)
  all_goals
    first
      | cases hTy
      | exact false_of_requires_eq_dtcapp_of_payload_ne_full (by intro hh; cases hh) hTy

private theorem false_of_typeof_strings_stoi_result_eq_dtcapp_full
    {y x A B : Term}
    (hTy :
      __eo_typeof__at_strings_stoi_result (__eo_typeof y) (__eo_typeof x) =
        Term.DtcAppType A B) :
    False := by
  cases hy : __eo_typeof y <;>
    simp [__eo_typeof__at_strings_stoi_result, hy] at hTy
  case Apply f T =>
    cases f <;> try cases hTy
    case UOp op =>
      cases op <;> try cases hTy
      case Seq =>
        cases T <;> try cases hTy
        case UOp op' =>
          cases op' <;> try cases hTy
          case Char =>
            cases hx : __eo_typeof x <;>
              simp [hx] at hTy
            case UOp op'' =>
              cases op'' <;> cases hTy

private theorem false_of_typeof_strings_itos_result_eq_dtcapp_full
    {y x A B : Term}
    (hTy : __eo_typeof_div (__eo_typeof y) (__eo_typeof x) = Term.DtcAppType A B) :
    False := by
  cases hy : __eo_typeof y <;> simp [__eo_typeof_div, hy] at hTy
  case UOp op =>
    cases op <;> try cases hTy
    case Int =>
      cases hx : __eo_typeof x <;> simp [hx] at hTy
      case UOp op' =>
        cases op' <;> cases hTy

private theorem false_of_typeof_str_at_eq_dtcapp_full
    {y x A B : Term}
    (hTy : __eo_typeof_str_at (__eo_typeof y) (__eo_typeof x) = Term.DtcAppType A B) :
    False := by
  cases hy : __eo_typeof y <;> simp [__eo_typeof_str_at, hy] at hTy
  case Apply f T =>
    cases f <;> try cases hTy
    case UOp op =>
      cases op <;> try cases hTy
      case Seq =>
        cases hx : __eo_typeof x <;> simp [hx] at hTy
        case UOp op' =>
          cases op' <;> cases hTy

private theorem false_of_typeof_is_eq_dtcapp_full
    {y x A B : Term}
    (hTy : __eo_typeof_is (__eo_typeof y) (__eo_typeof x) = Term.DtcAppType A B) :
    False := by
  cases hy : __eo_typeof y <;> simp [__eo_typeof_is, hy] at hTy
  all_goals
    cases hx : __eo_typeof x <;> simp [hx] at hTy

private theorem false_of_typeof_int_to_bv_eq_dtcapp_full
    {y x A B : Term}
    (hTy :
      __eo_typeof_int_to_bv (__eo_typeof y) y (__eo_typeof x) =
        Term.DtcAppType A B) :
    False := by
  unfold __eo_typeof_int_to_bv at hTy
  repeat (first | split at hTy)
  all_goals
    first
      | cases hTy
      | exact false_of_requires_eq_dtcapp_of_payload_ne_full
          (eo_apply_ne_dtcapp_full _ _ A B)
          hTy

private theorem eo_type_valid_of_set_choose_eq_dtcapp_full
    {x A B : Term}
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) ∧
          eo_type_valid (__eo_typeof x))
    (hTermNN :
      term_has_non_none_type
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_choose) x)))
    (hTy : __eo_typeof_set_choose (__eo_typeof x) = Term.DtcAppType A B) :
    eo_type_valid (Term.DtcAppType A B) := by
  have hMapNN :
      term_has_non_none_type
        (SmtTerm.map_diff (__eo_to_smt x)
          (SmtTerm.set_empty
            (__eo_to_smt_set_elem_type (__smtx_typeof (__eo_to_smt x))))) := by
    change
      term_has_non_none_type
        (SmtTerm.map_diff (__eo_to_smt x)
          (SmtTerm.set_empty
            (__eo_to_smt_set_elem_type (__smtx_typeof (__eo_to_smt x))))) at hTermNN
    exact hTermNN
  have hxNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rcases map_diff_args_of_non_none hMapNN with hMap | hSet
    · rcases hMap with ⟨M, N, hxTy, _hEmptyTy, _hDiffTy⟩
      rw [hxTy]
      simp
    · rcases hSet with ⟨T, hxTy, _hEmptyTy, _hDiffTy⟩
      rw [hxTy]
      simp
  have hxValid := (ihX hxNN).2
  have hNotStuck : __eo_typeof_set_choose (__eo_typeof x) ≠ Term.Stuck := by
    rw [hTy]
    simp
  rcases eo_typeof_set_choose_arg_set_full hNotStuck with
    ⟨T, hxSet⟩
  have hTValid : eo_type_valid T :=
    eo_type_valid_set_element_full T (by simpa [hxSet] using hxValid)
  rw [hxSet] at hTy
  simp [__eo_typeof_set_choose] at hTy
  rw [hTy] at hTValid
  exact hTValid

private theorem eo_type_valid_of_select_eq_dtcapp_full
    {y x A B : Term}
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y) ∧
          eo_type_valid (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) ∧
          eo_type_valid (__eo_typeof x))
    (hTermNN :
      term_has_non_none_type
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.select) y) x)))
    (hTy :
      __eo_typeof_select (__eo_typeof y) (__eo_typeof x) =
        Term.DtcAppType A B) :
    eo_type_valid (Term.DtcAppType A B) := by
  have hSelectNN :
      term_has_non_none_type (SmtTerm.select (__eo_to_smt y) (__eo_to_smt x)) := by
    change
      term_has_non_none_type (SmtTerm.select (__eo_to_smt y) (__eo_to_smt x))
        at hTermNN
    exact hTermNN
  rcases select_args_of_non_none hSelectNN with ⟨SA, SB, hYMap, hXArg⟩
  have hCompsRec :=
    Smtm.smt_map_components_wf_rec_of_non_none_type
      (__eo_to_smt y) SA SB hYMap
  have hSAWF : smtx_type_field_wf_rec SA native_reflist_nil :=
    smtx_type_field_wf_rec_of_type_wf_rec hCompsRec.1
  have hSANN : SA ≠ SmtType.None := by
    intro hNone
    rw [hNone] at hCompsRec
    simpa [__smtx_type_wf_rec] using hCompsRec.1
  have hYNN : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
    rw [hYMap]
    simp
  have hYAll := ihY hYNN
  have hYTypeSmt :
      __eo_to_smt_type (__eo_typeof y) = SmtType.Map SA SB :=
    hYAll.1.symm.trans hYMap
  rcases eo_to_smt_type_eq_map hYTypeSmt with
    ⟨U, T, hYArray, hU, hT⟩
  have hXNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hXArg]
    exact hSANN
  have hXTypeSmt : __eo_to_smt_type (__eo_typeof x) = SA :=
    (ihX hXNN).1.symm.trans hXArg
  have hXU : __eo_typeof x = U :=
    eo_to_smt_type_injective_of_field_wf_rec hXTypeSmt hU hSAWF
  have hUNN : __eo_to_smt_type U ≠ SmtType.None := by
    rw [hU]
    exact hSANN
  have hUNS : U ≠ Term.Stuck :=
    eo_term_ne_stuck_of_smt_type_non_none U hUNN
  have hTIs : T = Term.DtcAppType A B := by
    rw [hYArray, hXU] at hTy
    cases U <;>
      simp [__eo_typeof_select, __eo_requires, __eo_eq, native_ite,
        native_teq, native_not] at hTy hUNS ⊢ <;>
      exact hTy
  have hTValid : eo_type_valid T :=
    (eo_type_valid_map_components_full U T (by
      rw [← hYArray]
      exact hYAll.2)).2
  rw [hTIs] at hTValid
  exact hTValid

private theorem eo_type_valid_of_tuple_select_eq_dtcapp_full
    {x y A B : Term}
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) ∧
          eo_type_valid (__eo_typeof x))
    (hTermNN :
      term_has_non_none_type
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.tuple_select y) x)))
    (hTy :
      __eo_typeof_tuple_select (__eo_typeof y) y (__eo_typeof x) =
        Term.DtcAppType A B) :
    eo_type_valid (Term.DtcAppType A B) := by
  cases hTupleTy : __smtx_typeof (__eo_to_smt x) with
  | Datatype s d =>
      by_cases hs : s = (native_string_lit "@Tuple")
      · subst s
        have hDecl : ∃ body, d = __eo_to_smt_tuple_decl body := by
          cases d with
          | nil =>
              exfalso
              apply hTermNN
              change
                __smtx_typeof
                    (__eo_to_smt_tuple_select
                      (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y)
                      (__eo_to_smt x)) = SmtType.None
              rw [hTupleTy]
              cases __eo_to_smt y <;> simp [__eo_to_smt_tuple_select]
          | cons s2 body rest =>
              cases rest with
              | nil =>
                  by_cases hs2 : s2 = native_string_lit "@Tuple"
                  · subst s2
                    exact ⟨body, rfl⟩
                  · exfalso
                    apply hTermNN
                    change
                      __smtx_typeof
                          (__eo_to_smt_tuple_select
                            (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y)
                            (__eo_to_smt x)) = SmtType.None
                    rw [hTupleTy]
                    cases __eo_to_smt y <;>
                      simp [__eo_to_smt_tuple_select, hs2, native_streq,
                        native_and, native_ite]
              | cons s3 body3 rest3 =>
                  exfalso
                  apply hTermNN
                  change
                    __smtx_typeof
                        (__eo_to_smt_tuple_select
                          (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y)
                          (__eo_to_smt x)) = SmtType.None
                  rw [hTupleTy]
                  cases __eo_to_smt y <;> simp [__eo_to_smt_tuple_select]
        rcases hDecl with ⟨body, rfl⟩
        let tupleDD := __eo_to_smt_tuple_decl body
        cases hIdx : __eo_to_smt y with
        | Numeral n =>
            cases hNonneg : native_zleq 0 n
            · exfalso
              apply hTermNN
              change
                __smtx_typeof
                    (__eo_to_smt_tuple_select
                      (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y)
                      (__eo_to_smt x)) =
                  SmtType.None
              rw [hTupleTy, hIdx]
              simp [__eo_to_smt_tuple_select, __eo_to_smt_tuple_decl,
                hNonneg, native_streq,
                native_and, native_ite]
            · have hTranslate :
                  __eo_to_smt
                      (Term.Apply (Term.UOp1 UserOp1.tuple_select y) x) =
                    SmtTerm.Apply
                      (SmtTerm.DtSel (native_string_lit "@Tuple") tupleDD native_nat_zero
                        (native_int_to_nat n))
                      (__eo_to_smt x) := by
                change
                  __eo_to_smt_tuple_select
                      (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y)
                      (__eo_to_smt x) =
                    SmtTerm.Apply
                      (SmtTerm.DtSel (native_string_lit "@Tuple") tupleDD native_nat_zero
                        (native_int_to_nat n))
                      (__eo_to_smt x)
                rw [hTupleTy, hIdx]
                simp [__eo_to_smt_tuple_select, __eo_to_smt_tuple_decl,
                  tupleDD, hNonneg, native_streq,
                  native_and, native_ite]
              have hApplyNN :
                  term_has_non_none_type
                    (SmtTerm.Apply
                      (SmtTerm.DtSel (native_string_lit "@Tuple") tupleDD native_nat_zero
                        (native_int_to_nat n))
                      (__eo_to_smt x)) := by
                unfold term_has_non_none_type at hTermNN ⊢
                rw [← hTranslate]
                exact hTermNN
              have hArgTy :
                  __smtx_typeof (__eo_to_smt x) =
                    SmtType.Datatype (native_string_lit "@Tuple") tupleDD :=
                dt_sel_arg_datatype_of_non_none hApplyNN
              have hXNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
                rw [hArgTy]
                simp
              have hXAll := ihX hXNN
              have hTyFromIH :
                  __eo_to_smt_type (__eo_typeof x) =
                    SmtType.Datatype (native_string_lit "@Tuple") tupleDD :=
                hXAll.1.symm.trans hArgTy
              have hTyBody :
                  __eo_to_smt_type (__eo_typeof x) =
                    SmtType.Datatype (native_string_lit "@Tuple")
                      (__eo_to_smt_tuple_decl body) := by
                simpa [tupleDD] using hTyFromIH
              have hYN : y = Term.Numeral n :=
                eo_to_smt_eq_numeral y n hIdx
              subst y
              have hList :
                  __eo_is_list (Term.UOp UserOp.Tuple) (__eo_typeof x) =
                    Term.Boolean true :=
                eo_tuple_is_list_true_of_smt_tuple_type hTyBody
              have hSelectedEq :
                  __eo_list_nth_rec (__eo_typeof x) (Term.Numeral n) =
                    Term.DtcAppType A B := by
                have hNth :
                    __eo_list_nth (Term.UOp UserOp.Tuple) (__eo_typeof x)
                        (Term.Numeral n) =
                      Term.DtcAppType A B := by
                  have hTNS : __eo_typeof x ≠ Term.Stuck :=
                    eo_term_ne_stuck_of_smt_type_non_none (__eo_typeof x) (by
                      rw [hTyFromIH]
                      simp)
                  have hSel :
                      __eo_typeof_tuple_select (Term.UOp UserOp.Int)
                          (Term.Numeral n) (__eo_typeof x) =
                        __eo_list_nth (Term.UOp UserOp.Tuple)
                          (__eo_typeof x) (Term.Numeral n) :=
                    eo_typeof_tuple_select_of_non_stuck_full
                      (Term.Numeral n) (__eo_typeof x)
                      (by intro h; cases h) hTNS
                  change
                    __eo_typeof_tuple_select (Term.UOp UserOp.Int)
                        (Term.Numeral n) (__eo_typeof x) =
                      Term.DtcAppType A B at hTy
                  rw [hSel] at hTy
                  exact hTy
                simpa [__eo_list_nth, __eo_requires, hList, native_ite,
                  native_teq, native_not, SmtEval.native_not] using hNth
              have hXValidRec : eo_type_valid_rec [] (__eo_typeof x) :=
                eo_type_valid_rec_of_tuple_smt_type hTyBody hXAll.2
              have hRetNN :
                  __smtx_ret_typeof_sel (native_string_lit "@Tuple") tupleDD native_nat_zero
                      (native_int_to_nat n) ≠
                    SmtType.None := by
                have hSmt :
                    __smtx_typeof
                        (SmtTerm.Apply
                          (SmtTerm.DtSel (native_string_lit "@Tuple") tupleDD native_nat_zero
                            (native_int_to_nat n))
                          (__eo_to_smt x)) =
                      __smtx_ret_typeof_sel (native_string_lit "@Tuple") tupleDD native_nat_zero
                        (native_int_to_nat n) :=
                  dt_sel_term_typeof_of_non_none hApplyNN
                unfold term_has_non_none_type at hApplyNN
                rw [hSmt] at hApplyNN
                exact hApplyNN
              have hBound :
                  native_int_to_nat n <
                    __smtx_dt_num_sels body native_nat_zero := by
                have hBoundResolved :
                    native_int_to_nat n <
                      __smtx_dt_num_sels
                        (__smtx_dt_resolve
                          (__smtx_dd_lookup (native_string_lit "@Tuple") tupleDD)
                          tupleDD)
                        native_nat_zero := by
                  exact
                    ret_typeof_sel_rec_non_none_implies_lt
                      (__smtx_dt_resolve
                        (__smtx_dd_lookup (native_string_lit "@Tuple") tupleDD)
                        tupleDD)
                      native_nat_zero
                      (native_int_to_nat n) (by
                        simpa [__smtx_ret_typeof_sel] using hRetNN)
                have hLookup :
                    __smtx_dd_lookup (native_string_lit "@Tuple") tupleDD = body := by
                  simp [tupleDD, __eo_to_smt_tuple_decl, __smtx_dd_lookup,
                    native_streq, SmtEval.native_streq, native_ite]
                have hResolve := smtx_dt_resolve_tuple_body_eq
                  (T := __eo_typeof x) (d := body) hTyBody tupleDD
                rw [hLookup, hResolve] at hBoundResolved
                exact hBoundResolved
              have hSelectedValidNat :
                  eo_type_valid_rec []
                    (__eo_list_nth_rec (__eo_typeof x)
                      (Term.Numeral
                        (native_nat_to_int (native_int_to_nat n)))) :=
                eo_type_valid_rec_tuple_list_nth_rec_nat
                  (T := __eo_typeof x) (d := body)
                  (native_int_to_nat n) hTyBody hXValidRec hBound
              have hnNonneg : (0 : Int) ≤ n := by
                simpa [native_zleq, SmtEval.native_zleq] using hNonneg
              have hNatInt :
                  native_nat_to_int (native_int_to_nat n) = n := by
                simp [native_nat_to_int, native_int_to_nat,
                  Smtm.native_nat_to_int, SmtEval.native_int_to_nat,
                  Int.toNat_of_nonneg hnNonneg]
              have hSelectedValid :
                  eo_type_valid_rec []
                    (__eo_list_nth_rec (__eo_typeof x) (Term.Numeral n)) := by
                simpa [hNatInt] using hSelectedValidNat
              rw [hSelectedEq] at hSelectedValid
              exact eo_type_valid_of_valid_rec_top_full hSelectedValid
        | _ =>
            exfalso
            apply hTermNN
            change
              __smtx_typeof
                  (__eo_to_smt_tuple_select
                    (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y)
                    (__eo_to_smt x)) =
                SmtType.None
            rw [hTupleTy, hIdx]
            simp [__eo_to_smt_tuple_select]
      · exfalso
        apply hTermNN
        change
          __smtx_typeof
              (__eo_to_smt_tuple_select
                (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y)
                (__eo_to_smt x)) =
            SmtType.None
        rw [hTupleTy]
        cases d with
        | nil =>
            cases __eo_to_smt y <;> simp [__eo_to_smt_tuple_select]
        | cons s2 body rest =>
            cases rest with
            | nil =>
                cases __eo_to_smt y <;>
                  simp [__eo_to_smt_tuple_select, hs, native_streq,
                    native_and, native_ite]
            | cons s3 body3 rest3 =>
                cases __eo_to_smt y <;> simp [__eo_to_smt_tuple_select]
  | _ =>
      exfalso
      apply hTermNN
      change
        __smtx_typeof
            (__eo_to_smt_tuple_select
              (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y)
              (__eo_to_smt x)) =
          SmtType.None
      rw [hTupleTy]
      simp [__eo_to_smt_tuple_select]

private theorem eo_type_valid_of_seq_nth_eq_dtcapp_full
    {y x A B : Term}
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y) ∧
          eo_type_valid (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) ∧
          eo_type_valid (__eo_typeof x))
    (hNN :
      term_has_non_none_type
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) y) x)))
    (hTy :
      __eo_typeof_seq_nth (__eo_typeof y) (__eo_typeof x) =
        Term.DtcAppType A B) :
    eo_type_valid (Term.DtcAppType A B) := by
  have hApplyNN :
      term_has_non_none_type (SmtTerm.seq_nth (__eo_to_smt y) (__eo_to_smt x)) := by
    simpa [__eo_to_smt] using hNN
  rcases seq_nth_args_of_non_none hApplyNN with ⟨T, hYSeq, hXInt⟩
  have hYNN : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
    rw [hYSeq]
    simp
  have hXNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hXInt]
    simp
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih y (fun h => (ihY h).1) hYSeq with
    ⟨U, hYU, _hU⟩
  have hXTy : __eo_typeof x = Term.UOp UserOp.Int :=
    eo_typeof_eq_int_of_smt_int_from_ih x (fun h => (ihX h).1) hXInt
  have hUValid : eo_type_valid U :=
    eo_type_valid_seq_element_full U (by
      rw [← hYU]
      exact (ihY hYNN).2)
  have hUEq : U = Term.DtcAppType A B := by
    rw [hYU, hXTy] at hTy
    simpa [__eo_typeof_seq_nth] using hTy
  rw [← hUEq]
  exact hUValid

private theorem eo_to_smt_uop1_ne_dt_sel_full
    (op : UserOp1) (y : Term)
    (s : native_String) (d : SmtDatatypeDecl) (i j : native_Nat) :
    __eo_to_smt (Term.UOp1 op y) ≠ SmtTerm.DtSel s d i j := by
  intro h
  cases op <;> try cases h
  case seq_empty =>
    change __eo_to_smt_seq_empty (__eo_to_smt_type y) = SmtTerm.DtSel s d i j at h
    cases hTy : __eo_to_smt_type y <;> simp [__eo_to_smt_seq_empty, hTy] at h
  case set_empty =>
    change __eo_to_smt_set_empty (__eo_to_smt_type y) = SmtTerm.DtSel s d i j at h
    cases hTy : __eo_to_smt_type y <;> simp [__eo_to_smt_set_empty, hTy] at h

private theorem eo_to_smt_uop1_ne_dt_tester_full
    (op : UserOp1) (y : Term)
    (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    __eo_to_smt (Term.UOp1 op y) ≠ SmtTerm.DtTester s d i := by
  intro h
  cases op <;> try cases h
  case seq_empty =>
    change __eo_to_smt_seq_empty (__eo_to_smt_type y) = SmtTerm.DtTester s d i at h
    cases hTy : __eo_to_smt_type y <;> simp [__eo_to_smt_seq_empty, hTy] at h
  case set_empty =>
    change __eo_to_smt_set_empty (__eo_to_smt_type y) = SmtTerm.DtTester s d i at h
    cases hTy : __eo_to_smt_type y <;> simp [__eo_to_smt_set_empty, hTy] at h

private theorem smtx_apply_head_non_none_of_non_special_full
    (f x : SmtTerm)
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i)
    (hNN : __smtx_typeof (SmtTerm.Apply f x) ≠ SmtType.None) :
    __smtx_typeof f ≠ SmtType.None := by
  have hApply :
      __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠
        SmtType.None := by
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

private theorem eo_type_valid_of_generic_apply_eq_dtcapp_full
    {f x A B : Term}
    (ihF :
      __smtx_typeof (__eo_to_smt f) ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt f) = __eo_to_smt_type (__eo_typeof f) ∧
          eo_type_valid (__eo_typeof f))
    (hSel : ∀ s d i j, __eo_to_smt f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, __eo_to_smt f ≠ SmtTerm.DtTester s d i)
    (hTranslate :
      __eo_to_smt (Term.Apply f x) =
        SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x))
    (hEoApply :
      __eo_typeof (Term.Apply f x) =
        __eo_typeof_apply (__eo_typeof f) (__eo_typeof x))
    (hNN : term_has_non_none_type (__eo_to_smt (Term.Apply f x)))
    (hTy : __eo_typeof (Term.Apply f x) = Term.DtcAppType A B) :
    eo_type_valid (Term.DtcAppType A B) := by
  have hApplyNN :
      __smtx_typeof (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x)) ≠
        SmtType.None := by
    unfold term_has_non_none_type at hNN
    rw [← hTranslate]
    exact hNN
  have hFNN : __smtx_typeof (__eo_to_smt f) ≠ SmtType.None :=
    smtx_apply_head_non_none_of_non_special_full
      (__eo_to_smt f) (__eo_to_smt x) hSel hTester hApplyNN
  exact eo_type_valid_of_typeof_apply_eq_dtcapp_full (ihF hFNN).2 (by
    rw [← hEoApply]
    simpa using hTy)

private theorem eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
    {g y x A B : Term}
    (ihGY :
      __smtx_typeof (__eo_to_smt (Term.Apply g y)) ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt (Term.Apply g y)) =
            __eo_to_smt_type (__eo_typeof (Term.Apply g y)) ∧
          eo_type_valid (__eo_typeof (Term.Apply g y)))
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply g y) x) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply g y)) (__eo_to_smt x))
    (hEoApply :
      __eo_typeof (Term.Apply (Term.Apply g y) x) =
        __eo_typeof_apply (__eo_typeof (Term.Apply g y)) (__eo_typeof x))
    (hNN : term_has_non_none_type (__eo_to_smt (Term.Apply (Term.Apply g y) x)))
    (hTy :
      __eo_typeof (Term.Apply (Term.Apply g y) x) = Term.DtcAppType A B) :
    eo_type_valid (Term.DtcAppType A B) := by
  exact eo_type_valid_of_generic_apply_eq_dtcapp_full
    (f := Term.Apply g y) (x := x) (A := A) (B := B)
    (ihF := ihGY)
    (hSel := by
      intro s d i j h
      exact (eo_to_smt_apply_ne_dt_sel g y s d i j h).elim)
    (hTester := by
      intro s d i h
      exact (eo_to_smt_apply_ne_dt_tester g y s d i h).elim)
    (hTranslate := hTranslate)
    (hEoApply := hEoApply)
    (hNN := hNN)
    (hTy := hTy)

private theorem eo_to_smt_apply_apply_apply_uop_generic_full
    (op : UserOp) (z y x : Term)
    (hIte : op ≠ UserOp.ite)
    (hStore : op ≠ UserOp.store)
    (hBvite : op ≠ UserOp.bvite)
    (hStrSubstr : op ≠ UserOp.str_substr)
    (hStrReplace : op ≠ UserOp.str_replace)
    (hStrIndexof : op ≠ UserOp.str_indexof)
    (hStrUpdate : op ≠ UserOp.str_update)
    (hStrReplaceAll : op ≠ UserOp.str_replace_all)
    (hStrReplaceRe : op ≠ UserOp.str_replace_re)
    (hStrReplaceReAll : op ≠ UserOp.str_replace_re_all)
    (hStrIndexofRe : op ≠ UserOp.str_indexof_re)
    (hStringsOccurIndex : op ≠ UserOp._at_strings_occur_index)
    (hStringsOccurIndexRe : op ≠ UserOp._at_strings_occur_index_re) :
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x) =
        SmtTerm.Apply
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y))
          (__eo_to_smt x) := by
  cases op <;>
    first
      | rfl
      | exact False.elim (hIte rfl)
      | exact False.elim (hStore rfl)
      | exact False.elim (hBvite rfl)
      | exact False.elim (hStrSubstr rfl)
      | exact False.elim (hStrReplace rfl)
      | exact False.elim (hStrIndexof rfl)
      | exact False.elim (hStrUpdate rfl)
      | exact False.elim (hStrReplaceAll rfl)
      | exact False.elim (hStrReplaceRe rfl)
      | exact False.elim (hStrReplaceReAll rfl)
      | exact False.elim (hStrIndexofRe rfl)
      | exact False.elim (hStringsOccurIndex rfl)
      | exact False.elim (hStringsOccurIndexRe rfl)

private theorem eo_typeof_apply_apply_apply_uop_generic_full
    (op : UserOp) (z y x : Term)
    (hIte : op ≠ UserOp.ite)
    (hStore : op ≠ UserOp.store)
    (hBvite : op ≠ UserOp.bvite)
    (hStrSubstr : op ≠ UserOp.str_substr)
    (hStrReplace : op ≠ UserOp.str_replace)
    (hStrIndexof : op ≠ UserOp.str_indexof)
    (hStrUpdate : op ≠ UserOp.str_update)
    (hStrReplaceAll : op ≠ UserOp.str_replace_all)
    (hStrReplaceRe : op ≠ UserOp.str_replace_re)
    (hStrReplaceReAll : op ≠ UserOp.str_replace_re_all)
    (hStrIndexofRe : op ≠ UserOp.str_indexof_re)
    (hStringsOccurIndex : op ≠ UserOp._at_strings_occur_index)
    (hStringsOccurIndexRe : op ≠ UserOp._at_strings_occur_index_re) :
      __eo_typeof
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x) =
        __eo_typeof_apply
          (__eo_typeof (Term.Apply (Term.Apply (Term.UOp op) z) y))
          (__eo_typeof x) := by
  cases op <;>
    first
      | rfl
      | exact False.elim (hIte rfl)
      | exact False.elim (hStore rfl)
      | exact False.elim (hBvite rfl)
      | exact False.elim (hStrSubstr rfl)
      | exact False.elim (hStrReplace rfl)
      | exact False.elim (hStrIndexof rfl)
      | exact False.elim (hStrUpdate rfl)
      | exact False.elim (hStrReplaceAll rfl)
      | exact False.elim (hStrReplaceRe rfl)
      | exact False.elim (hStrReplaceReAll rfl)
      | exact False.elim (hStrIndexofRe rfl)
      | exact False.elim (hStringsOccurIndex rfl)
      | exact False.elim (hStringsOccurIndexRe rfl)

private theorem eo_type_valid_of_generic_apply_typeof_apply_eq_dtcapp_full
    {f x A B : Term}
    (ihF :
      __smtx_typeof (__eo_to_smt f) ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt f) = __eo_to_smt_type (__eo_typeof f) ∧
          eo_type_valid (__eo_typeof f))
    (hSel : ∀ s d i j, __eo_to_smt f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, __eo_to_smt f ≠ SmtTerm.DtTester s d i)
    (hTranslate :
      __eo_to_smt (Term.Apply f x) =
        SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x))
    (hNN : term_has_non_none_type (__eo_to_smt (Term.Apply f x)))
    (hTy :
      __eo_typeof_apply (__eo_typeof f) (__eo_typeof x) = Term.DtcAppType A B) :
    eo_type_valid (Term.DtcAppType A B) := by
  have hApplyNN :
      __smtx_typeof (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x)) ≠
        SmtType.None := by
    unfold term_has_non_none_type at hNN
    rw [← hTranslate]
    exact hNN
  have hFNN : __smtx_typeof (__eo_to_smt f) ≠ SmtType.None :=
    smtx_apply_head_non_none_of_non_special_full
      (__eo_to_smt f) (__eo_to_smt x) hSel hTester hApplyNN
  exact eo_type_valid_of_typeof_apply_eq_dtcapp_full (ihF hFNN).2 hTy

private theorem eo_type_valid_of_nested_generic_apply_typeof_apply_eq_dtcapp_full
    {g y x A B : Term}
    (ihGY :
      __smtx_typeof (__eo_to_smt (Term.Apply g y)) ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt (Term.Apply g y)) =
            __eo_to_smt_type (__eo_typeof (Term.Apply g y)) ∧
          eo_type_valid (__eo_typeof (Term.Apply g y)))
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply g y) x) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply g y)) (__eo_to_smt x))
    (hNN : term_has_non_none_type (__eo_to_smt (Term.Apply (Term.Apply g y) x)))
    (hTy :
      __eo_typeof_apply (__eo_typeof (Term.Apply g y)) (__eo_typeof x) =
        Term.DtcAppType A B) :
    eo_type_valid (Term.DtcAppType A B) := by
  exact eo_type_valid_of_generic_apply_typeof_apply_eq_dtcapp_full
    (f := Term.Apply g y) (x := x) (A := A) (B := B)
    ihGY
    (by
      intro s d i j h
      exact (eo_to_smt_apply_ne_dt_sel g y s d i j h).elim)
    (by
      intro s d i h
      exact (eo_to_smt_apply_ne_dt_tester g y s d i h).elim)
    hTranslate hNN hTy

private theorem smtx_typeof_guard_ne_dtcapp_of_ne
    {T U A B : SmtType}
    (hU : U ≠ SmtType.DtcAppType A B) :
    __smtx_typeof_guard T U ≠ SmtType.DtcAppType A B := by
  unfold __smtx_typeof_guard
  cases native_Teq T SmtType.None <;> simp [native_ite, hU]

private theorem native_ite_none_ne_dtcapp_of_ne
    {c : native_Bool} {U A B : SmtType}
    (hU : U ≠ SmtType.DtcAppType A B) :
    native_ite c U SmtType.None ≠ SmtType.DtcAppType A B := by
  cases c <;> simp [native_ite, hU]

private theorem eo_to_smt_type_apply_ne_dtcapp
    (a b : Term) (A B : SmtType) :
    __eo_to_smt_type (Term.Apply a b) ≠ SmtType.DtcAppType A B := by
  intro h
  cases a
  case UOp op =>
    cases op
    case BitVec =>
      cases b <;> simp [__eo_to_smt_type] at h
      case Numeral n =>
        exact native_ite_none_ne_dtcapp_of_ne (by intro h'; cases h') h
    case Seq =>
      exact smtx_typeof_guard_ne_dtcapp_of_ne (by intro h'; cases h') h
    case Set =>
      exact smtx_typeof_guard_ne_dtcapp_of_ne (by intro h'; cases h') h
    all_goals
      simp [__eo_to_smt_type] at h
  case Apply g y =>
    cases g
    case FunType =>
      exact smtx_typeof_guard_ne_dtcapp_of_ne
        (smtx_typeof_guard_ne_dtcapp_of_ne (by intro h'; cases h')) h
    case UOp op =>
      cases op
      case Array =>
        exact smtx_typeof_guard_ne_dtcapp_of_ne
          (smtx_typeof_guard_ne_dtcapp_of_ne (by intro h'; cases h')) h
      case Tuple =>
        exact native_ite_none_ne_dtcapp_of_ne
          (eo_to_smt_type_tuple_ne_dtc_app (__eo_to_smt_type y) (__eo_to_smt_type b) A B) h
      all_goals
        simp [__eo_to_smt_type] at h
    all_goals
      simp [__eo_to_smt_type] at h
  all_goals
    simp [__eo_to_smt_type] at h

private theorem false_of_eq_eo_dtcapp_type_of_no_smt_dtcapp_full
    {t : SmtTerm} {a b : Term}
    (hEq : __smtx_typeof t = __eo_to_smt_type (Term.DtcAppType a b))
    (hNN : __eo_to_smt_type (Term.DtcAppType a b) ≠ SmtType.None)
    (hNe : ∀ A B, __smtx_typeof t ≠ SmtType.DtcAppType A B) :
    False := by
  change
    __smtx_typeof t =
      __smtx_typeof_guard (__eo_to_smt_type a)
        (__smtx_typeof_guard (__eo_to_smt_type b)
          (SmtType.DtcAppType (__eo_to_smt_type a) (__eo_to_smt_type b))) at hEq
  change
    __smtx_typeof_guard (__eo_to_smt_type a)
        (__smtx_typeof_guard (__eo_to_smt_type b)
          (SmtType.DtcAppType (__eo_to_smt_type a) (__eo_to_smt_type b))) ≠
      SmtType.None at hNN
  cases hA : __eo_to_smt_type a <;> cases hB : __eo_to_smt_type b <;>
    simp [__smtx_typeof_guard, native_ite, native_Teq, hA, hB] at hEq hNN
  all_goals
    exact hNe _ _ hEq

private theorem smtx_typeof_apply_dt_sel_ne_dtcapp_full
    (s : native_String) (d : SmtDatatypeDecl) (i j : native_Nat)
    (x : SmtTerm) (A B : SmtType) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s d i j) x) ≠
      SmtType.DtcAppType A B := by
  intro h
  cases hR : __smtx_ret_typeof_sel s d i j <;>
    simp [__smtx_typeof_guard_wf, __smtx_type_wf, __smtx_type_wf_rec,
      __smtx_typeof, __smtx_typeof_apply, __smtx_typeof_guard,
      native_and, native_ite, native_Teq, hR] at h
  all_goals
    repeat split at h
    all_goals cases h

private theorem eo_to_smt_apply_dt_sel_ne_dtcapp_full
    (s : native_String) (d : DatatypeDecl) (i j : native_Nat) (x : Term)
    (A B : SmtType) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.DtSel s d i j) x)) ≠
      SmtType.DtcAppType A B := by
  intro h
  change
    __smtx_typeof
        (SmtTerm.Apply
          (native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
            (SmtTerm.DtSel s (__eo_to_smt_datatype_decl d) i j))
          (__eo_to_smt x)) =
      SmtType.DtcAppType A B at h
  cases hRes : __eo_to_smt_reserved_datatype_name s
  · simp [native_ite, hRes] at h
    exact smtx_typeof_apply_dt_sel_ne_dtcapp_full s (__eo_to_smt_datatype_decl d) i j
      (__eo_to_smt x) A B h
  · simp [native_ite, hRes, __smtx_typeof, __smtx_typeof_apply] at h

private theorem smtx_typeof_extract_ne_dtcapp_full
    (hi lo x : SmtTerm) (A B : SmtType) :
    __smtx_typeof (SmtTerm.extract hi lo x) ≠ SmtType.DtcAppType A B := by
  intro h
  rw [typeof_extract_eq] at h
  cases hi <;> try simp [__smtx_typeof_extract] at h
  case Numeral hi =>
    cases lo <;> try simp at h
    case Numeral lo =>
      cases hx : __smtx_typeof x <;>
        simp [hx] at h
      all_goals
        repeat split at h
        all_goals cases h


/-- Reduction of skolemization on a `cons` binder list at a successor index. -/
private theorem eo_to_smt_quantifiers_skolemize_succ_cons
    (s : native_String) (T vs : Term) (G : SmtTerm) (n : native_Nat) :
    __eo_to_smt_quantifiers_skolemize
        (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) vs) G n.succ =
      __eo_to_smt_quantifiers_skolemize vs
        (SmtTerm.bind s (__eo_to_smt_type T)
          (SmtTerm.choice s (__eo_to_smt_type T) (__eo_to_smt_exists vs G)) G) n := by
  simp [__eo_to_smt_quantifiers_skolemize]

/-- A true EO list check implies the underlying nil search is non-stuck. -/
private theorem eo_get_nil_rec_ok_of_is_list_true
    (xs : Term) :
    __eo_is_list Term.__eo_List_cons xs = Term.Boolean true ->
    __eo_is_ok (__eo_get_nil_rec Term.__eo_List_cons xs) = Term.Boolean true := by
  intro h
  cases xs <;>
    simp [__eo_is_list, __eo_get_nil_rec, __eo_is_ok, __eo_requires,
      __eo_is_list_nil, native_ite, native_teq, native_not] at h ⊢
  all_goals exact h

/-- SMT existential translation only typechecks for syntactic EO variable lists. -/
private theorem eo_is_list_of_exists_bool
    (xs : Term) (body : SmtTerm) :
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool ->
    __eo_is_list Term.__eo_List_cons xs = Term.Boolean true := by
  intro hTy
  cases hxs : xs
  case __eo_List_nil =>
    subst hxs
    native_decide
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
              change
                __smtx_typeof
                    (__eo_to_smt_exists
                      (Term.Apply (Term.Apply Term.__eo_List_cons
                        (Term.Var (Term.String s) T)) a) body) =
                  SmtType.Bool at hTy
              rw [eo_to_smt_exists_cons] at hTy
              change
                __smtx_typeof
                    (SmtTerm.exists s (__eo_to_smt_type T) (__eo_to_smt_exists a body)) =
                  SmtType.Bool at hTy
              exact hTy
            have hNN :
                term_has_non_none_type (SmtTerm.exists s (__eo_to_smt_type T) (__eo_to_smt_exists a body)) := by
              unfold term_has_non_none_type
              rw [hExistsTy]
              simp
            have hSub : __smtx_typeof (__eo_to_smt_exists a body) = SmtType.Bool := by
              simpa using exists_body_bool_of_non_none hNN
            have hTailList := eo_is_list_of_exists_bool a body hSub
            have hTailOk := eo_get_nil_rec_ok_of_is_list_true a hTailList
            change
              __eo_is_list Term.__eo_List_cons
                  (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) a) =
                Term.Boolean true
            simpa [__eo_is_list, __eo_get_nil_rec, __eo_requires, native_ite,
              native_teq, native_not] using hTailOk
          all_goals
            subst hname
            have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
              simp [smtx_typeof_none, __eo_to_smt_exists] at hTy ⊢
            exact False.elim (smtx_typeof_none_ne_bool hNone)
        all_goals
          subst hy
          have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
            simp [smtx_typeof_none, __eo_to_smt_exists] at hTy ⊢
          exact False.elim (smtx_typeof_none_ne_bool hNone)
      all_goals
        subst hg
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          simp [smtx_typeof_none, __eo_to_smt_exists] at hTy ⊢
        exact False.elim (smtx_typeof_none_ne_bool hNone)
    all_goals
      subst hf
      have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
        simp [smtx_typeof_none, __eo_to_smt_exists] at hTy ⊢
      exact False.elim (smtx_typeof_none_ne_bool hNone)
  all_goals
    subst hxs
    have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
      simp [smtx_typeof_none, __eo_to_smt_exists] at hTy ⊢
    exact False.elim (smtx_typeof_none_ne_bool hNone)

/-- The head variable is the zeroth element of a translated EO variable list. -/
private theorem get_var_type_list_nth_zero_cons_var_of_exists_bool
    (s : native_String) (T a : Term) (body : SmtTerm)
    (hTailBool : __smtx_typeof (__eo_to_smt_exists a body) = SmtType.Bool) :
    __get_var_type
        (__eo_list_nth Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) a)
          (Term.Numeral (native_nat_to_int 0))) =
      T := by
  have hTailList := eo_is_list_of_exists_bool a body hTailBool
  have hTailOk := eo_get_nil_rec_ok_of_is_list_true a hTailList
  have hFullList :
      __eo_is_list Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) a) =
        Term.Boolean true := by
    simpa [__eo_is_list, __eo_get_nil_rec, __eo_requires, native_ite,
      native_teq, native_not] using hTailOk
  change
    __get_var_type
        (__eo_requires
          (__eo_is_list Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) a))
          (Term.Boolean true)
          (__eo_list_nth_rec
            (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) a)
            (Term.Numeral (native_nat_to_int 0)))) =
      T
  rw [hFullList]
  rfl

/-- Successor list indexing through a translated EO variable-list cons. -/
private theorem get_var_type_list_nth_succ_cons_var_of_exists_bool
    (s : native_String) (T a : Term) (body : SmtTerm) (n : native_Nat)
    (hTailBool : __smtx_typeof (__eo_to_smt_exists a body) = SmtType.Bool) :
    __get_var_type
        (__eo_list_nth Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) a)
          (Term.Numeral (native_nat_to_int n.succ))) =
      __get_var_type
        (__eo_list_nth Term.__eo_List_cons a (Term.Numeral (native_nat_to_int n))) := by
  have hTailList := eo_is_list_of_exists_bool a body hTailBool
  have hTailOk := eo_get_nil_rec_ok_of_is_list_true a hTailList
  have hFullList :
      __eo_is_list Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) a) =
        Term.Boolean true := by
    simpa [__eo_is_list, __eo_get_nil_rec, __eo_requires, native_ite,
      native_teq, native_not] using hTailOk
  change
    __get_var_type
        (__eo_requires
          (__eo_is_list Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) a))
          (Term.Boolean true)
          (__eo_list_nth_rec
            (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) a)
            (Term.Numeral (native_nat_to_int n.succ)))) =
      __get_var_type
        (__eo_requires (__eo_is_list Term.__eo_List_cons a) (Term.Boolean true)
          (__eo_list_nth_rec a (Term.Numeral (native_nat_to_int n))))
  rw [hFullList, hTailList]
  change
    __get_var_type
        (__eo_list_nth_rec a
          (__eo_add (Term.Numeral (native_nat_to_int n.succ))
            (Term.Numeral (-1 : native_Int)))) =
      __get_var_type (__eo_list_nth_rec a (Term.Numeral (native_nat_to_int n)))
  change
    __get_var_type
        (__eo_list_nth_rec a
          (Term.Numeral (native_zplus (native_nat_to_int n.succ) (-1 : native_Int)))) =
      __get_var_type (__eo_list_nth_rec a (Term.Numeral (native_nat_to_int n)))
  rw [show native_zplus (native_nat_to_int n.succ) (-1 : native_Int) =
      native_nat_to_int n by
    simp [native_zplus, native_nat_to_int]
    calc
      (↑n + 1 + -1 : Int) = ↑n + (1 + -1) := by ac_rfl
      _ = ↑n := by rfl]

private theorem smtx_typeof_eo_to_smt_exists_cons_bool_of_tail_bool
    (s : native_String) (T a : Term) (body : SmtTerm)
    (hWf : __smtx_type_wf (__eo_to_smt_type T) = true)
    (hTailBool : __smtx_typeof (__eo_to_smt_exists a body) = SmtType.Bool) :
    __smtx_typeof
        (__eo_to_smt_exists
          (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) a)
          body) =
      SmtType.Bool := by
  rw [eo_to_smt_exists_cons]
  change
    __smtx_typeof
        (SmtTerm.exists s (__eo_to_smt_type T) (__eo_to_smt_exists a body)) =
      SmtType.Bool
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [hTailBool, native_ite, native_Teq, __smtx_typeof_guard_wf, hWf]

/-- Typing equation for a `bind` node. -/
private theorem typeof_bind_eq_full
    (s : native_String) (T : SmtType) (x1 x2 : SmtTerm) :
    __smtx_typeof (SmtTerm.bind s T x1 x2) =
      native_ite (native_Teq (__smtx_typeof x1) T)
        (__smtx_typeof_guard_wf T (__smtx_typeof x2)) SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only

/-- Typing equation for an `exists` node. -/
private theorem typeof_exists_eq_full
    (s : native_String) (T : SmtType) (x1 : SmtTerm) :
    __smtx_typeof (SmtTerm.exists s T x1) =
      native_ite (native_Teq (__smtx_typeof x1) SmtType.Bool)
        (__smtx_typeof_guard_wf T SmtType.Bool) SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only

/-- The type of an `exists` node depends on its body only through the body's type. -/
private theorem typeof_smt_exists_congr
    (s : native_String) (T : SmtType) (X Y : SmtTerm)
    (h : __smtx_typeof X = __smtx_typeof Y) :
    __smtx_typeof (SmtTerm.exists s T X) = __smtx_typeof (SmtTerm.exists s T Y) := by
  rw [typeof_exists_eq_full, typeof_exists_eq_full, h]

/-- The type of a translated existential chain depends on its body only through
the body's type: swapping bodies of equal type preserves the chain type. -/
private theorem exists_chain_body_congr
    (vs : Term) (A B : SmtTerm)
    (hAB : __smtx_typeof A = __smtx_typeof B) :
    __smtx_typeof (__eo_to_smt_exists vs A) = __smtx_typeof (__eo_to_smt_exists vs B) := by
  cases hvs : vs
  case __eo_List_nil =>
    subst hvs
    simpa [__eo_to_smt_exists] using hAB
  case Apply f a =>
    subst hvs
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
            rw [eo_to_smt_exists_cons, eo_to_smt_exists_cons]
            exact typeof_smt_exists_congr s (__eo_to_smt_type T) _ _
              (exists_chain_body_congr a A B hAB)
          all_goals
            subst hname
            simp [__eo_to_smt_exists]
        all_goals
          subst hy
          simp [__eo_to_smt_exists]
      all_goals
        subst hg
        simp [__eo_to_smt_exists]
    all_goals
      subst hf
      simp [__eo_to_smt_exists]
  all_goals
    subst hvs
    simp [__eo_to_smt_exists]

/-- Any well-typed skolemization forces the enclosing existential chain to be
Boolean.  In the `bind`-threaded successor recursion the body is re-wrapped as
`G' = bind s T (choice s T (exists vs G)) G`; the recursion recovers Boolean-ness
of the chain over `G'`, from which we recover it for the original `G` by peeling
the `bind` (which forces the head binder well-formed and `typeof G = typeof G'`)
and the body-swap congruence above. -/
private theorem eo_to_smt_exists_bool_of_quantifiers_skolemize_non_none
    (xs : Term) (body : SmtTerm) (n : native_Nat)
    (hBodyNoExists : ∀ s T F, body ≠ SmtTerm.exists s T F) :
    __smtx_typeof (__eo_to_smt_quantifiers_skolemize xs body n) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool := by
  induction n generalizing xs body with
  | zero =>
      intro hNN
      cases xs with
      | Apply f a =>
        cases f with
        | Apply g y =>
          cases g with
          | __eo_List_cons =>
            cases y with
            | Var name T =>
              cases name with
              | String s =>
                  rw [eo_to_smt_quantifiers_skolemize_zero] at hNN
                  have hChoiceNN :
                      term_has_non_none_type
                        (SmtTerm.choice s (__eo_to_smt_type T) (__eo_to_smt_exists a body)) := hNN
                  have hTailBool := choice_nth_body_bool_of_non_none hChoiceNN
                  have hGuardTy := choice_term_guard_type_of_non_none hChoiceNN
                  have hGuardNN :
                      __smtx_typeof_guard_wf (__eo_to_smt_type T) (__eo_to_smt_type T) ≠
                        SmtType.None := by
                    intro hNone
                    unfold term_has_non_none_type at hChoiceNN
                    exact hChoiceNN (by rw [hGuardTy, hNone])
                  have hWf : __smtx_type_wf (__eo_to_smt_type T) = true :=
                    Smtm.smtx_typeof_guard_wf_wf_of_non_none
                      (__eo_to_smt_type T) (__eo_to_smt_type T) hGuardNN
                  exact smtx_typeof_eo_to_smt_exists_cons_bool_of_tail_bool s T a body hWf hTailBool
              | _ => simp [__eo_to_smt_quantifiers_skolemize] at hNN
            | _ => simp [__eo_to_smt_quantifiers_skolemize] at hNN
          | _ => simp [__eo_to_smt_quantifiers_skolemize] at hNN
        | _ => simp [__eo_to_smt_quantifiers_skolemize] at hNN
      | _ => simp [__eo_to_smt_quantifiers_skolemize] at hNN
  | succ n ih =>
      intro hNN
      cases xs with
      | Apply f a =>
        cases f with
        | Apply g y =>
          cases g with
          | __eo_List_cons =>
            cases y with
            | Var name T =>
              cases name with
              | String s =>
                  rw [eo_to_smt_quantifiers_skolemize_succ_cons] at hNN
                  have hG'NoExists :
                      ∀ s' T' F',
                        SmtTerm.bind s (__eo_to_smt_type T)
                            (SmtTerm.choice s (__eo_to_smt_type T) (__eo_to_smt_exists a body)) body ≠
                          SmtTerm.exists s' T' F' := by
                    intro s' T' F' h
                    cases h
                  have hTailG' := ih a _ hG'NoExists hNN
                  have hG'Bool := eo_to_smt_exists_body_bool_of_bool a _ hTailG'
                  have hBindNN :
                      term_has_non_none_type
                        (SmtTerm.bind s (__eo_to_smt_type T)
                          (SmtTerm.choice s (__eo_to_smt_type T) (__eo_to_smt_exists a body)) body) := by
                    unfold term_has_non_none_type
                    rw [hG'Bool]
                    simp
                  have hBindTy := Smtm.bind_term_typeof_of_non_none hBindNN
                  have hGuardNN :
                      __smtx_typeof_guard_wf (__eo_to_smt_type T) (__smtx_typeof body) ≠
                        SmtType.None := by
                    intro hNone
                    have hbn :
                        __smtx_typeof
                          (SmtTerm.bind s (__eo_to_smt_type T)
                            (SmtTerm.choice s (__eo_to_smt_type T) (__eo_to_smt_exists a body)) body) =
                          SmtType.None := by
                      rw [typeof_bind_eq_full, hNone]
                      cases hcond :
                          native_Teq
                            (__smtx_typeof
                              (SmtTerm.choice s (__eo_to_smt_type T) (__eo_to_smt_exists a body)))
                            (__eo_to_smt_type T) <;>
                        simp [native_ite]
                    exact absurd hbn hBindNN
                  have hWf : __smtx_type_wf (__eo_to_smt_type T) = true :=
                    Smtm.smtx_typeof_guard_wf_wf_of_non_none
                      (__eo_to_smt_type T) (__smtx_typeof body) hGuardNN
                  have hCong := exists_chain_body_congr a _ body hBindTy
                  have hTailBool : __smtx_typeof (__eo_to_smt_exists a body) = SmtType.Bool := by
                    rw [← hCong]
                    exact hTailG'
                  exact smtx_typeof_eo_to_smt_exists_cons_bool_of_tail_bool s T a body hWf hTailBool
              | _ => simp [__eo_to_smt_quantifiers_skolemize] at hNN
            | _ => simp [__eo_to_smt_quantifiers_skolemize] at hNN
          | _ => simp [__eo_to_smt_quantifiers_skolemize] at hNN
        | _ => simp [__eo_to_smt_quantifiers_skolemize] at hNN
      | _ => simp [__eo_to_smt_quantifiers_skolemize] at hNN

/-- Computes the selected binder type for quantifier skolemization. -/
private theorem eo_to_smt_quantifiers_skolemize_type_of_non_none
    (xs : Term) (body : SmtTerm) (n : native_Nat)
    (hBodyNoExists : ∀ s T F, body ≠ SmtTerm.exists s T F) :
    __smtx_typeof (__eo_to_smt_quantifiers_skolemize xs body n) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt_quantifiers_skolemize xs body n) =
      __eo_to_smt_type
        (__get_var_type (__eo_list_nth Term.__eo_List_cons xs (Term.Numeral (native_nat_to_int n)))) := by
  induction n generalizing xs body with
  | zero =>
      intro hNN
      cases xs with
      | Apply f a =>
        cases f with
        | Apply g y =>
          cases g with
          | __eo_List_cons =>
            cases y with
            | Var name T =>
              cases name with
              | String s =>
                  rw [eo_to_smt_quantifiers_skolemize_zero] at hNN ⊢
                  have hChoiceNN :
                      term_has_non_none_type
                        (SmtTerm.choice s (__eo_to_smt_type T) (__eo_to_smt_exists a body)) := hNN
                  have hBodyBool := choice_nth_body_bool_of_non_none hChoiceNN
                  have hTy := choice_term_typeof_of_non_none hChoiceNN
                  have hNth :=
                    get_var_type_list_nth_zero_cons_var_of_exists_bool s T a body hBodyBool
                  rw [hTy, hNth]
              | _ => simp [__eo_to_smt_quantifiers_skolemize] at hNN
            | _ => simp [__eo_to_smt_quantifiers_skolemize] at hNN
          | _ => simp [__eo_to_smt_quantifiers_skolemize] at hNN
        | _ => simp [__eo_to_smt_quantifiers_skolemize] at hNN
      | _ => simp [__eo_to_smt_quantifiers_skolemize] at hNN
  | succ n ih =>
      intro hNN
      cases xs with
      | Apply f a =>
        cases f with
        | Apply g y =>
          cases g with
          | __eo_List_cons =>
            cases y with
            | Var name T =>
              cases name with
              | String s =>
                  rw [eo_to_smt_quantifiers_skolemize_succ_cons] at hNN ⊢
                  have hG'NoExists :
                      ∀ s' T' F',
                        SmtTerm.bind s (__eo_to_smt_type T)
                            (SmtTerm.choice s (__eo_to_smt_type T) (__eo_to_smt_exists a body)) body ≠
                          SmtTerm.exists s' T' F' := by
                    intro s' T' F' h
                    cases h
                  have hExistsBool :=
                    eo_to_smt_exists_bool_of_quantifiers_skolemize_non_none a _ n hG'NoExists hNN
                  have ih' := ih a _ hG'NoExists hNN
                  have hNth :=
                    get_var_type_list_nth_succ_cons_var_of_exists_bool s T a _ n hExistsBool
                  rw [ih', hNth]
              | _ => simp [__eo_to_smt_quantifiers_skolemize] at hNN
            | _ => simp [__eo_to_smt_quantifiers_skolemize] at hNN
          | _ => simp [__eo_to_smt_quantifiers_skolemize] at hNN
        | _ => simp [__eo_to_smt_quantifiers_skolemize] at hNN
      | _ => simp [__eo_to_smt_quantifiers_skolemize] at hNN

/-- The selected binder type in a well-typed skolemization is a valid EO type. -/
private theorem eo_to_smt_quantifiers_skolemize_var_type_valid_of_non_none
    (xs : Term) (body : SmtTerm) (n : native_Nat)
    (hBodyNoExists : ∀ s T F, body ≠ SmtTerm.exists s T F) :
    __smtx_typeof (__eo_to_smt_quantifiers_skolemize xs body n) ≠
      SmtType.None ->
    eo_type_valid
      (__get_var_type
        (__eo_list_nth Term.__eo_List_cons xs (Term.Numeral (native_nat_to_int n)))) := by
  induction n generalizing xs body with
  | zero =>
      intro hNN
      cases xs with
      | Apply f a =>
        cases f with
        | Apply g y =>
          cases g with
          | __eo_List_cons =>
            cases y with
            | Var name T =>
              cases name with
              | String s =>
                  rw [eo_to_smt_quantifiers_skolemize_zero] at hNN
                  have hChoiceNN :
                      term_has_non_none_type
                        (SmtTerm.choice s (__eo_to_smt_type T) (__eo_to_smt_exists a body)) := hNN
                  have hBodyBool := choice_nth_body_bool_of_non_none hChoiceNN
                  have hGuardTy := choice_term_guard_type_of_non_none hChoiceNN
                  have hGuardNN :
                      __smtx_typeof_guard_wf (__eo_to_smt_type T) (__eo_to_smt_type T) ≠
                        SmtType.None := by
                    intro hNone
                    unfold term_has_non_none_type at hChoiceNN
                    exact hChoiceNN (by rw [hGuardTy, hNone])
                  have hNth :=
                    get_var_type_list_nth_zero_cons_var_of_exists_bool s T a body hBodyBool
                  rw [hNth]
                  exact eo_type_valid_of_guard_wf_non_none_full (T := T) (U := T) hGuardNN
              | _ => simp [__eo_to_smt_quantifiers_skolemize] at hNN
            | _ => simp [__eo_to_smt_quantifiers_skolemize] at hNN
          | _ => simp [__eo_to_smt_quantifiers_skolemize] at hNN
        | _ => simp [__eo_to_smt_quantifiers_skolemize] at hNN
      | _ => simp [__eo_to_smt_quantifiers_skolemize] at hNN
  | succ n ih =>
      intro hNN
      cases xs with
      | Apply f a =>
        cases f with
        | Apply g y =>
          cases g with
          | __eo_List_cons =>
            cases y with
            | Var name T =>
              cases name with
              | String s =>
                  rw [eo_to_smt_quantifiers_skolemize_succ_cons] at hNN
                  have hG'NoExists :
                      ∀ s' T' F',
                        SmtTerm.bind s (__eo_to_smt_type T)
                            (SmtTerm.choice s (__eo_to_smt_type T) (__eo_to_smt_exists a body)) body ≠
                          SmtTerm.exists s' T' F' := by
                    intro s' T' F' h
                    cases h
                  have hExistsBool :=
                    eo_to_smt_exists_bool_of_quantifiers_skolemize_non_none a _ n hG'NoExists hNN
                  have hValid := ih a _ hG'NoExists hNN
                  have hNth :=
                    get_var_type_list_nth_succ_cons_var_of_exists_bool s T a _ n hExistsBool
                  rw [hNth]
                  exact hValid
              | _ => simp [__eo_to_smt_quantifiers_skolemize] at hNN
            | _ => simp [__eo_to_smt_quantifiers_skolemize] at hNN
          | _ => simp [__eo_to_smt_quantifiers_skolemize] at hNN
        | _ => simp [__eo_to_smt_quantifiers_skolemize] at hNN
      | _ => simp [__eo_to_smt_quantifiers_skolemize] at hNN


/-- Strong induction form: translation typing plus proof-side validity. -/
private theorem eo_to_smt_typeof_matches_translation_and_valid
    (t : Term) :
    __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t) ∧
      eo_type_valid (__eo_typeof t) := by
  let rec go : (term : Term) ->
      __smtx_typeof (__eo_to_smt term) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt term) = __eo_to_smt_type (__eo_typeof term) ∧
        eo_type_valid (__eo_typeof term)
    | Term.UOp op, hNonNone => by
        cases op
        case re_allchar =>
          refine ⟨?_, ?_⟩
          · rw [eo_to_smt_re_allchar, eo_typeof_re_allchar, eo_to_smt_type_reglan]
            unfold __smtx_typeof
            rfl
          · simp [eo_typeof_re_allchar, eo_type_valid]
        case re_none =>
          refine ⟨?_, ?_⟩
          · rw [eo_to_smt_re_none, eo_typeof_re_none, eo_to_smt_type_reglan]
            unfold __smtx_typeof
            rfl
          · simp [eo_typeof_re_none, eo_type_valid]
        case re_all =>
          refine ⟨?_, ?_⟩
          · rw [eo_to_smt_re_all, eo_typeof_re_all, eo_to_smt_type_reglan]
            unfold __smtx_typeof
            rfl
          · simp [eo_typeof_re_all, eo_type_valid]
        case tuple_unit =>
          refine ⟨?_, ?_⟩
          · rw [eo_to_smt_term_tuple_unit, smtx_typeof_tuple_unit_translation,
              eo_typeof_tuple_unit, eo_to_smt_type_unit_tuple]
          · simp [eo_typeof_tuple_unit, eo_type_valid]
        all_goals
          exact false_of_smtx_typeof_none_non_none_full hNonNone
    | Term.UOp1 UserOp1.repeat x, hNonNone => by
        exact false_of_smtx_typeof_none_non_none_full hNonNone
    | Term.UOp1 UserOp1.zero_extend x, hNonNone => by
        exact false_of_smtx_typeof_none_non_none_full hNonNone
    | Term.UOp1 UserOp1.sign_extend x, hNonNone => by
        exact false_of_smtx_typeof_none_non_none_full hNonNone
    | Term.UOp1 UserOp1.rotate_left x, hNonNone => by
        exact false_of_smtx_typeof_none_non_none_full hNonNone
    | Term.UOp1 UserOp1.rotate_right x, hNonNone => by
        exact false_of_smtx_typeof_none_non_none_full hNonNone
    | Term.UOp1 UserOp1._at_bit x, hNonNone => by
        exact false_of_smtx_typeof_none_non_none_full hNonNone
    | Term.UOp1 UserOp1.re_exp x, hNonNone => by
        exact false_of_smtx_typeof_none_non_none_full hNonNone
    | Term.UOp1 UserOp1.is x, hNonNone => by
        exact false_of_smtx_typeof_none_non_none_full hNonNone
    | Term.UOp1 UserOp1.update x, hNonNone => by
        exact false_of_smtx_typeof_none_non_none_full hNonNone
    | Term.UOp1 UserOp1.tuple_select x, hNonNone => by
        exact false_of_smtx_typeof_none_non_none_full hNonNone
    | Term.UOp1 UserOp1.tuple_update x, hNonNone => by
        exact false_of_smtx_typeof_none_non_none_full hNonNone
    | Term.UOp1 UserOp1.int_to_bv x, hNonNone => by
        exact false_of_smtx_typeof_none_non_none_full hNonNone
    | Term.UOp2 UserOp2.extract x y, hNonNone => by
        exact false_of_smtx_typeof_none_non_none_full hNonNone
    | Term.UOp2 UserOp2.re_loop x y, hNonNone => by
        exact false_of_smtx_typeof_none_non_none_full hNonNone
    | Term.Boolean b, hNonNone => by
        refine ⟨?_, ?_⟩
        · rw [eo_to_smt_boolean, eo_typeof_boolean, eo_to_smt_type_bool]
          unfold __smtx_typeof
          rfl
        · simp [eo_typeof_boolean, eo_type_valid]
    | Term.Numeral n, hNonNone => by
        have hSmt : __smtx_typeof (__eo_to_smt (Term.Numeral n)) = SmtType.Int := by
          change __smtx_typeof (SmtTerm.Numeral n) = SmtType.Int
          unfold __smtx_typeof
          rfl
        refine ⟨hSmt.trans (eo_to_smt_type_typeof_numeral n).symm, ?_⟩
        change eo_type_valid (Term.UOp UserOp.Int)
        simp [eo_type_valid, noNoneTy]
    | Term.Rational r, hNonNone => by
        have hSmt : __smtx_typeof (__eo_to_smt (Term.Rational r)) = SmtType.Real := by
          change __smtx_typeof (SmtTerm.Rational r) = SmtType.Real
          unfold __smtx_typeof
          rfl
        refine ⟨hSmt.trans (eo_to_smt_type_typeof_rational r).symm, ?_⟩
        change eo_type_valid (Term.UOp UserOp.Real)
        simp [eo_type_valid]
    | Term.String s, hNonNone => by
        have hValid : native_string_valid s = true := by
          change __smtx_typeof (SmtTerm.String s) ≠ SmtType.None at hNonNone
          cases h : native_string_valid s
          · exfalso
            apply hNonNone
            unfold __smtx_typeof
            simp [native_ite, h]
          · rfl
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.String s)) = SmtType.Seq SmtType.Char := by
          change __smtx_typeof (SmtTerm.String s) = SmtType.Seq SmtType.Char
          unfold __smtx_typeof
          simp [native_ite, hValid]
        refine ⟨hSmt.trans (eo_to_smt_type_typeof_string s).symm, ?_⟩
        change eo_type_valid (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
        simp [eo_type_valid, noNoneTy,
          __smtx_typeof_guard, native_Teq]
    | Term.Binary w n, hNonNone => by
        have hWidth : native_zleq 0 w = true := by
          by_cases hw : native_zleq 0 w = true
          · exact hw
          · exfalso
            change __smtx_typeof (SmtTerm.Binary w n) ≠ SmtType.None at hNonNone
            apply hNonNone
            unfold __smtx_typeof
            simp [native_ite, SmtEval.native_and, hw]
        change __smtx_typeof (SmtTerm.Binary w n) ≠ SmtType.None at hNonNone
        have hSmt := smtx_typeof_binary_of_non_none w n
          hNonNone
        refine ⟨?_, ?_⟩
        · change __smtx_typeof (SmtTerm.Binary w n) =
            __eo_to_smt_type (__eo_typeof (Term.Binary w n))
          exact hSmt.trans (eo_to_smt_type_typeof_binary w n hWidth).symm
        · change eo_type_valid (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
          simp [eo_type_valid, hWidth]
    | Term.Var name T, hNonNone => by
        cases name with
        | String s =>
            change __smtx_typeof (SmtTerm.Var s (__eo_to_smt_type T)) ≠
              SmtType.None at hNonNone
            refine ⟨?_, ?_⟩
            · change __smtx_typeof (SmtTerm.Var s (__eo_to_smt_type T)) =
                __eo_to_smt_type (__eo_typeof (Term.Var (Term.String s) T))
              exact
                (smtx_typeof_var_of_non_none s (__eo_to_smt_type T) hNonNone).trans
                  (eo_to_smt_type_typeof_var s T).symm
            · exact eo_type_valid_of_guard_wf_non_none_full
                (T := T) (U := T) (by
                  simpa [__smtx_typeof] using hNonNone)
        | _ =>
            exact false_of_smtx_typeof_none_non_none_full hNonNone
    | Term.DtCons s d i, hNonNone => by
        have hReserved : __eo_reserved_datatype_name s = false := by
          cases hRes : __eo_reserved_datatype_name s
          · rfl
          · exfalso
            apply hNonNone
            rw [eo_to_smt_term_dt_cons, hRes]
            simp [native_ite]
        have hDtNN :
            __smtx_typeof
                (SmtTerm.DtCons s (__eo_to_smt_datatype_decl d) i) ≠
              SmtType.None := by
          change
            __smtx_typeof
                (native_ite (__eo_reserved_datatype_name s) SmtTerm.None
                  (SmtTerm.DtCons s (__eo_to_smt_datatype_decl d) i)) ≠
              SmtType.None at hNonNone
          rw [hReserved] at hNonNone
          exact hNonNone
        have hTy :=
          eo_to_smt_type_typeof_dt_cons_decl_of_non_none
            s d i hReserved hDtNN
        refine ⟨?_, ?_⟩
        · change
            __smtx_typeof
                (native_ite (__eo_reserved_datatype_name s) SmtTerm.None
                  (SmtTerm.DtCons s (__eo_to_smt_datatype_decl d) i)) =
              __eo_to_smt_type (__eo_typeof (Term.DtCons s d i))
          rw [hReserved]
          exact hTy.1.symm
        · exact eo_type_valid_of_valid_rec_top_full hTy.2
    | Term.UConst i T, hNonNone => by
        change __smtx_typeof (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T)) ≠
          SmtType.None at hNonNone
        refine ⟨?_, ?_⟩
        · change __smtx_typeof (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T)) =
            __eo_to_smt_type (__eo_typeof (Term.UConst i T))
          exact
            (smtx_typeof_uconst_of_non_none (native_uconst_id i) (__eo_to_smt_type T)
              hNonNone).trans
              (eo_to_smt_type_typeof_uconst i T).symm
        · exact eo_type_valid_of_guard_wf_non_none_full
            (T := T) (U := T) (by
              simpa [__smtx_typeof] using hNonNone)
    | Term.Apply f x, hNonNone => by
        by_cases hDistinct : f = Term.UOp UserOp.distinct
        case pos =>
          subst f
          have hElemNN :
              __eo_to_smt_typed_list_elem_type x ≠ SmtType.None := by
            intro hElemNone
            apply hNonNone
            change
              __smtx_typeof
                  (native_ite
                    (native_Teq (__eo_to_smt_typed_list_elem_type x) SmtType.None)
                    SmtTerm.None (__eo_to_smt_distinct x)) =
                SmtType.None
            simp [hElemNone, native_ite, native_Teq, smtx_typeof_none]
          have hElemGuard :
              native_Teq (__eo_to_smt_typed_list_elem_type x) SmtType.None =
                false :=
            native_Teq_none_false_of_non_none_full hElemNN
          have hDistinctNN :
              __smtx_typeof (__eo_to_smt_distinct x) ≠ SmtType.None := by
            change
              __smtx_typeof
                  (native_ite
                    (native_Teq (__eo_to_smt_typed_list_elem_type x) SmtType.None)
                    SmtTerm.None (__eo_to_smt_distinct x)) ≠
                SmtType.None at hNonNone
            rw [hElemGuard] at hNonNone
            exact hNonNone
          have hDistinctBool :
              __smtx_typeof (__eo_to_smt_distinct x) = SmtType.Bool :=
            smtx_typeof_eo_to_smt_distinct_of_non_none_full x hDistinctNN
          rcases eo_to_smt_typed_list_elem_type_of_non_none_full
              (Term.Apply (Term.UOp UserOp.distinct) x)
              (fun term hLt hNN => go term hNN)
              x (by simp) hElemNN with
            ⟨T, hXType, hXSmt, hTValid⟩
          refine ⟨?_, ?_⟩
          · change
              __smtx_typeof
                  (native_ite
                    (native_Teq (__eo_to_smt_typed_list_elem_type x) SmtType.None)
                    SmtTerm.None (__eo_to_smt_distinct x)) =
                __eo_to_smt_type (__eo_typeof_distinct (__eo_typeof x))
            rw [hElemGuard]
            change __smtx_typeof (__eo_to_smt_distinct x) =
              __eo_to_smt_type (__eo_typeof_distinct (__eo_typeof x))
            rw [hDistinctBool, hXType]
            rfl
          · change eo_type_valid (__eo_typeof_distinct (__eo_typeof x))
            rw [hXType]
            simp [__eo_typeof_distinct, eo_type_valid]
        case neg =>
          have hNotDistinct : f ≠ Term.UOp UserOp.distinct := hDistinct
          have hEq :=
            eo_to_smt_typeof_matches_translation_apply f x (go f) (go x)
              (fun op y h hNN => by
                subst f
                exact go y hNN)
              (fun g y h hNN => by
                subst f
                exact go y hNN)
              (fun g z y h hNN => by
                subst f
                exact go z hNN)
              (fun term _ hNN => go term hNN)
              hNotDistinct hNonNone
          refine ⟨hEq, ?_⟩
          have hTermNN :
              term_has_non_none_type (__eo_to_smt (Term.Apply f x)) := by
            unfold term_has_non_none_type
            exact hNonNone
          have hTypeNN :
              __eo_to_smt_type (__eo_typeof (Term.Apply f x)) ≠ SmtType.None := by
            rw [← hEq]
            exact hNonNone
          cases hTy : __eo_typeof (Term.Apply f x)
          case UOp op =>
            rw [hTy] at hTypeNN
            cases op <;>
              simp [eo_type_valid, __eo_to_smt_type] at hTypeNN ⊢
          case DatatypeType s d =>
            have hReserved : __eo_reserved_datatype_name s = false := by
              have hTypeNN' := hTypeNN
              rw [hTy] at hTypeNN'
              simpa [__eo_to_smt_type, native_ite] using hTypeNN'
            have hSmtTy :
                __smtx_typeof (__eo_to_smt (Term.Apply f x)) =
                  SmtType.Datatype s (__eo_to_smt_datatype_decl d) := by
              rw [hEq, hTy]
              simp [__eo_to_smt_type, native_ite, hReserved]
            exact eo_type_valid_of_smt_wf (Term.DatatypeType s d)
              (by
                simpa [__eo_to_smt_type, native_ite, hReserved] using
                  Smtm.smt_datatype_wf_of_non_none_type
                    (__eo_to_smt (Term.Apply f x)) s
                      (__eo_to_smt_datatype_decl d) hSmtTy)
          case DatatypeTypeRef s =>
            have hReserved : __eo_reserved_datatype_name s = false := by
              have hTypeNN' := hTypeNN
              rw [hTy] at hTypeNN'
              simpa [__eo_to_smt_type, native_ite] using hTypeNN'
            have hSmtTy :
                __smtx_typeof (__eo_to_smt (Term.Apply f x)) =
                  SmtType.TypeRef s := by
              rw [hEq, hTy]
              simp [__eo_to_smt_type, native_ite, hReserved]
            have hNoNone :=
              Smtm.term_type_has_no_none_components_of_non_none
                (__eo_to_smt (Term.Apply f x)) hTermNN
            rw [hSmtTy] at hNoNone
            exact False.elim (by
              simp [Smtm.type_has_no_none_components] at hNoNone)
          case UOp1 op y =>
            exact False.elim (hTypeNN (by
              rw [hTy]
              simp [__eo_to_smt_type]))
          case UOp2 op y z =>
            exact False.elim (hTypeNN (by
              rw [hTy]
              simp [__eo_to_smt_type]))
          case UOp3 op y z w =>
            exact False.elim (hTypeNN (by
              rw [hTy]
              simp [__eo_to_smt_type]))
          case __eo_List =>
            exact False.elim (hTypeNN (by
              rw [hTy]
              simp [__eo_to_smt_type]))
          case __eo_List_nil =>
            exact False.elim (hTypeNN (by
              rw [hTy]
              simp [__eo_to_smt_type]))
          case __eo_List_cons =>
            exact False.elim (hTypeNN (by
              rw [hTy]
              simp [__eo_to_smt_type]))
          case Bool =>
            simp [eo_type_valid]
          case Boolean b =>
            exact False.elim (hTypeNN (by
              rw [hTy]
              simp [__eo_to_smt_type]))
          case Numeral n =>
            exact False.elim (hTypeNN (by
              rw [hTy]
              simp [__eo_to_smt_type]))
          case Rational q =>
            exact False.elim (hTypeNN (by
              rw [hTy]
              simp [__eo_to_smt_type]))
          case String s =>
            exact False.elim (hTypeNN (by
              rw [hTy]
              simp [__eo_to_smt_type]))
          case Binary w n =>
            exact False.elim (hTypeNN (by
              rw [hTy]
              simp [__eo_to_smt_type]))
          case «Type» =>
            exact False.elim (hTypeNN (by
              rw [hTy]
              simp [__eo_to_smt_type]))
          case Stuck =>
            exact False.elim (hTypeNN (by
              rw [hTy]
              simp [__eo_to_smt_type]))
          case FunType =>
            exact False.elim (hTypeNN (by
              rw [hTy]
              simp [__eo_to_smt_type]))
          case Var name T =>
            exact False.elim (hTypeNN (by
              rw [hTy]
              simp [__eo_to_smt_type]))
          case DtCons s d i =>
            exact False.elim (hTypeNN (by
              rw [hTy]
              simp [__eo_to_smt_type]))
          case DtSel s d i j =>
            exact False.elim (hTypeNN (by
              rw [hTy]
              simp [__eo_to_smt_type]))
          case USort i =>
            change noNoneTy (SmtType.USort i) = true
            simp [noNoneTy]
          case UConst i T =>
            exact False.elim (hTypeNN (by
              rw [hTy]
              simp [__eo_to_smt_type]))
          case Apply a b =>
            have hSmtTy :
                __smtx_typeof (__eo_to_smt (Term.Apply f x)) =
                  __eo_to_smt_type (Term.Apply a b) := by
              rw [hEq, hTy]
            cases hSmt : __eo_to_smt_type (Term.Apply a b)
            case None =>
              exact False.elim (hTypeNN (by rw [hTy, hSmt]))
            case Bool =>
              simp [eo_type_valid, hSmt, noNoneTy]
            case Int =>
              simp [eo_type_valid, hSmt, noNoneTy]
            case Real =>
              simp [eo_type_valid, hSmt, noNoneTy]
            case RegLan =>
              simp [eo_type_valid, hSmt, noNoneTy]
            case BitVec w =>
              simp [eo_type_valid, hSmt, noNoneTy]
            case Map A B =>
              have hMapTy :
                  __smtx_typeof (__eo_to_smt (Term.Apply f x)) =
                    SmtType.Map A B := by
                simpa [hSmt] using hSmtTy
              exact eo_type_valid_of_smt_wf (Term.Apply a b)
                (by
                  simpa [hSmt] using
                    Smtm.smt_term_map_type_wf_of_non_none
                      (__eo_to_smt (Term.Apply f x)) hTermNN hMapTy)
            case Set A =>
              have hSetTy :
                  __smtx_typeof (__eo_to_smt (Term.Apply f x)) =
                    SmtType.Set A := by
                simpa [hSmt] using hSmtTy
              exact eo_type_valid_of_smt_wf (Term.Apply a b)
                (by
                  simpa [hSmt] using
                    Smtm.smt_term_set_type_wf_of_non_none
                      (__eo_to_smt (Term.Apply f x)) hTermNN hSetTy)
            case Seq A =>
              have hSeqTy :
                  __smtx_typeof (__eo_to_smt (Term.Apply f x)) =
                    SmtType.Seq A := by
                simpa [hSmt] using hSmtTy
              exact eo_type_valid_of_smt_wf (Term.Apply a b)
                (by
                  simpa [hSmt] using
                    Smtm.smt_term_seq_type_wf_of_non_none
                      (__eo_to_smt (Term.Apply f x)) hTermNN hSeqTy)
            case Char =>
              simp [eo_type_valid, hSmt, noNoneTy]
            case Datatype s d =>
              have hDatatypeTy :
                  __smtx_typeof (__eo_to_smt (Term.Apply f x)) =
                    SmtType.Datatype s d := by
                simpa [hSmt] using hSmtTy
              exact eo_type_valid_of_smt_wf (Term.Apply a b)
                (by
                  simpa [hSmt] using
                    Smtm.smt_datatype_wf_of_non_none_type
                      (__eo_to_smt (Term.Apply f x)) s d hDatatypeTy)
            case TypeRef s =>
              have hRefTy :
                  __smtx_typeof (__eo_to_smt (Term.Apply f x)) =
                    SmtType.TypeRef s := by
                simpa [hSmt] using hSmtTy
              have hNoNone :=
                Smtm.term_type_has_no_none_components_of_non_none
                  (__eo_to_smt (Term.Apply f x)) hTermNN
              rw [hRefTy] at hNoNone
              exact False.elim (by
                simp [Smtm.type_has_no_none_components] at hNoNone)
            case USort i =>
              simp [eo_type_valid, hSmt, noNoneTy]
            case FunType A B =>
              have hFunTy :
                  __smtx_typeof (__eo_to_smt (Term.Apply f x)) =
                    SmtType.FunType A B := by
                simpa [hSmt] using hSmtTy
              exact eo_type_valid_of_smt_wf (Term.Apply a b)
                (by
                  simpa [hSmt] using
                    Smtm.smt_term_fun_type_wf_of_non_none
                      (__eo_to_smt (Term.Apply f x)) hTermNN hFunTy)
            case DtcAppType A B =>
              exact False.elim (eo_to_smt_type_apply_ne_dtcapp a b A B hSmt)
          case DtcAppType a b =>
            cases f <;> try dsimp [__eo_typeof] at hTy <;> try cases hTy
            case UOp op =>
              cases op <;> dsimp [__eo_typeof] at hTy hTypeNN
              case _at_purify =>
                have hxNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
                  intro hNone
                  apply hNonNone
                  change __smtx_typeof (SmtTerm._at_purify (__eo_to_smt x)) =
                    SmtType.None
                  simpa [__smtx_typeof] using hNone
                have hxValid := (go x hxNN).2
                cases hxTy : __eo_typeof x <;>
                  simp [__eo_typeof__at_purify, hxTy] at hTy hTypeNN ⊢
                all_goals try cases hTy
                all_goals
                  subst_vars
                  simpa [eo_type_valid, eo_type_valid_rec, hxTy] using hxValid
              all_goals first
                | exact eo_type_valid_of_generic_apply_eq_dtcapp_full
                    (f := Term.UOp op) (x := x) (A := a) (B := b)
                    (go (Term.UOp op))
                    (by
                      intro s d i j h
                      cases op <;> simp [__eo_to_smt] at h)
                    (by
                      intro s d i h
                      cases op <;> simp [__eo_to_smt] at h)
                    rfl rfl hTermNN (by
                      change
                        __eo_typeof_apply (__eo_typeof (Term.UOp1 op y))
                            (__eo_typeof x) =
                          Term.DtcAppType a b
                      exact hTy)
                | exact eo_type_valid_of_typeof_apply_eq_dtcapp_cond_cases_full
                    (by intro T U h hU; cases h <;> cases hU)
                    (by intro T U h hU; cases h <;> cases hU)
                    hTy
                | exact False.elim (false_of_typeof_BitVec_eq_dtcapp_full hTy)
                | exact False.elim (false_of_typeof_typed_list_nil_eq_dtcapp_full hTy)
                | exact False.elim (false_of_typeof_distinct_eq_dtcapp_full hTy)
                | exact False.elim (false_of_typeof_to_real_eq_dtcapp_full hTy)
                | exact False.elim (false_of_typeof_to_int_eq_dtcapp_full hTy)
                | exact False.elim (false_of_typeof_is_int_eq_dtcapp_full hTy)
                | exact False.elim (false_of_typeof_abs_eq_dtcapp_full hTy)
                | exact False.elim (false_of_typeof_int_pow2_eq_dtcapp_full hTy)
                | exact False.elim (false_of_typeof_int_ispow2_eq_dtcapp_full hTy)
                | exact False.elim (false_of_typeof_at_bvsize_eq_dtcapp_full hTy)
                | exact False.elim (false_of_typeof_bvnot_eq_dtcapp_full hTy)
                | exact False.elim (false_of_typeof_bvnego_eq_dtcapp_full hTy)
                | exact False.elim (false_of_typeof_bvredand_eq_dtcapp_full hTy)
                | exact False.elim (false_of_typeof_str_len_eq_dtcapp_full hTy)
                | exact False.elim (false_of_typeof_str_rev_eq_dtcapp_full hTy)
                | exact False.elim (false_of_typeof_str_to_lower_eq_dtcapp_full hTy)
                | exact False.elim (false_of_typeof_str_to_code_eq_dtcapp_full hTy)
                | exact False.elim (false_of_typeof_str_from_code_eq_dtcapp_full hTy)
                | exact False.elim (false_of_typeof_str_is_digit_eq_dtcapp_full hTy)
                | exact False.elim (false_of_typeof_str_to_re_eq_dtcapp_full hTy)
                | exact False.elim (false_of_typeof_re_mult_eq_dtcapp_full hTy)
                | exact False.elim (false_of_typeof_seq_unit_eq_dtcapp_full hTy)
                | exact False.elim (false_of_typeof_set_singleton_eq_dtcapp_full hTy)
                | exact eo_type_valid_of_set_choose_eq_dtcapp_full
                    (go x) hTermNN hTy
                | exact False.elim (false_of_typeof_set_is_empty_eq_dtcapp_full hTy)
                | exact False.elim (false_of_typeof_div_by_zero_eq_dtcapp_full hTy)
                | simp [eo_type_valid,
                    
                    __eo_typeof_Seq,
                    __eo_typeof_not
                    
                    
                    
                    
                    
                    
                    
                    
                    
                    
                    
                    ] at hTy hTypeNN ⊢
                  cases hxTy : __eo_typeof x <;>
                    simp [hxTy
                      
                      
                      
                      
                      
                      
                      
                      
                      
                      
                      
                      
                      
                      
                      ] at hTy hTypeNN ⊢
                  all_goals try cases hTy
            case UOp1 op y =>
              cases op <;> dsimp [__eo_typeof] at hTy hTypeNN
              case seq_empty =>
                exact False.elim (hNonNone (by
                  change
                    __smtx_typeof
                        (SmtTerm.Apply (__eo_to_smt_seq_empty (__eo_to_smt_type y))
                          (__eo_to_smt x)) =
                      SmtType.None
                  exact typeof_apply_eo_to_smt_seq_empty_eq_none
                    (__eo_to_smt_type y) (__eo_to_smt x)))
              case tuple_select =>
                exact eo_type_valid_of_tuple_select_eq_dtcapp_full
                  (go x) hTermNN hTy
              case set_empty =>
                exact False.elim (hNonNone (by
                  change
                    __smtx_typeof
                        (SmtTerm.Apply (__eo_to_smt_set_empty (__eo_to_smt_type y))
                          (__eo_to_smt x)) =
                      SmtType.None
                  exact typeof_apply_eo_to_smt_set_empty_eq_none
                    (__eo_to_smt_type y) (__eo_to_smt x)))
              all_goals first
                | exact eo_type_valid_of_generic_apply_eq_dtcapp_full
                    (f := Term.UOp1 op y) (x := x) (A := a) (B := b)
                    (go (Term.UOp1 op y))
                    (by
                      intro s d i j h
                      exact eo_to_smt_uop1_ne_dt_sel_full op y s d i j h)
                    (by
                      intro s d i h
                      exact eo_to_smt_uop1_ne_dt_tester_full op y s d i h)
                    rfl rfl hTermNN (by
                      change
                        __eo_typeof (Term.Apply (Term.UOp1 op y) x) =
                          Term.DtcAppType a b
                      exact hTy)
                | exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
                    (by intro T U h; cases h)
                    (by intro T U h; cases h)
                    hTy
                | exact False.elim (false_of_typeof_repeat_eq_dtcapp_full hTy)
                | exact False.elim (false_of_typeof_zero_extend_eq_dtcapp_full hTy)
                | exact False.elim (false_of_typeof_rotate_left_eq_dtcapp_full hTy)
                | exact False.elim (false_of_typeof_at_bit2_eq_dtcapp_full hTy)
                | exact False.elim (false_of_typeof_re_exp_eq_dtcapp_full hTy)
                | exact False.elim (false_of_typeof_strings_stoi_result_eq_dtcapp_full hTy)
                | exact False.elim (false_of_typeof_strings_itos_result_eq_dtcapp_full hTy)
                | exact False.elim (false_of_typeof_str_at_eq_dtcapp_full hTy)
                | exact False.elim (false_of_typeof_is_eq_dtcapp_full hTy)
                | exact False.elim (false_of_typeof_int_to_bv_eq_dtcapp_full hTy)
                | simp [eo_type_valid, eo_type_valid_rec, __eo_to_smt_type,
                    __eo_typeof_apply, __eo_requires, __eo_typeof__at_purify,
                    __eo_typeof_repeat, __eo_typeof_zero_extend,
                    __eo_typeof_rotate_left, __eo_typeof__at_bit,
                    __eo_typeof_seq_empty, __eo_typeof_re_exp,
                    __eo_typeof__at_strings_stoi_result,
                    __eo_typeof_str_to_code, __eo_typeof_div,
                    __eo_typeof_str_at, __eo_typeof_is,
                    __eo_typeof_tuple_select, __eo_typeof_set_empty,
                    __eo_typeof_int_to_bv, __eo_mk_apply, __eo_requires,
                    __eo_add, __eo_mul, __is_arith_type, __eo_eq, native_ite,
                    native_teq, native_not] at hTy hTypeNN ⊢
            case UOp2 op y z =>
              cases op <;> dsimp [__eo_typeof] at hTy hTypeNN
              case extract =>
                exact False.elim (false_of_eq_eo_dtcapp_type_of_no_smt_dtcapp_full
                  (t := SmtTerm.extract (__eo_to_smt y) (__eo_to_smt z)
                    (__eo_to_smt x))
                  (a := a) (b := b)
                  (by
                    change
                      __smtx_typeof
                          (__eo_to_smt
                            (Term.Apply (Term.UOp2 UserOp2.extract y z) x)) =
                        __eo_to_smt_type (Term.DtcAppType a b)
                    rw [hEq]
                    change
                      __eo_to_smt_type
                          (__eo_typeof_extract (__eo_typeof y) y (__eo_typeof z) z
                            (__eo_typeof x)) =
                        __eo_to_smt_type (Term.DtcAppType a b)
                    rw [hTy])
                  (by
                    intro hNone
                    apply hTypeNN
                    change
                      __eo_to_smt_type
                          (__eo_typeof_extract (__eo_typeof y) y (__eo_typeof z) z
                            (__eo_typeof x)) =
                        SmtType.None
                    rw [hTy]
                    exact hNone)
                  (smtx_typeof_extract_ne_dtcapp_full
                    (__eo_to_smt y) (__eo_to_smt z) (__eo_to_smt x)))
              case re_loop =>
                exact False.elim (false_of_typeof_re_loop_eq_dtcapp_full hTy)
              case _at_quantifiers_skolemize =>
                exact eo_type_valid_of_generic_apply_eq_dtcapp_full
                  (f := Term.UOp2 UserOp2._at_quantifiers_skolemize y z)
                  (x := x) (A := a) (B := b)
                  (go (Term.UOp2 UserOp2._at_quantifiers_skolemize y z))
                  (by
                    intro s d i j h
                    rcases eo_to_smt_eq_dt_sel_cases
                        (Term.UOp2 UserOp2._at_quantifiers_skolemize y z) s d i j h with
                      ⟨d0, hd, hTerm, hReserved⟩ | ⟨q, hTerm, hq⟩
                    · cases hTerm
                    · cases hTerm)
                  (by
                    intro s d i h
                    exact eo_to_smt_ne_dt_tester
                      (Term.UOp2 UserOp2._at_quantifiers_skolemize y z) s d i h)
                  rfl rfl hTermNN (by
                    change
                      __eo_typeof_apply
                          (__eo_typeof
                            (Term.UOp2 UserOp2._at_quantifiers_skolemize y z))
                          (__eo_typeof x) =
                        Term.DtcAppType a b
                    exact hTy)
              case _at_const =>
                exact eo_type_valid_of_generic_apply_eq_dtcapp_full
                  (f := Term.UOp2 UserOp2._at_const y z)
                  (x := x) (A := a) (B := b)
                  (go (Term.UOp2 UserOp2._at_const y z))
                  (by
                    intro s d i j h
                    exact eo_to_smt_at_const_ne_dt_sel y z s d i j h)
                  (by
                    intro s d i h
                    exact eo_to_smt_at_const_ne_dt_tester y z s d i h)
                  rfl rfl hTermNN (by
                    change
                      __eo_typeof_apply
                          (__eo_typeof (Term.UOp2 UserOp2._at_const y z))
                          (__eo_typeof x) =
                        Term.DtcAppType a b
                    exact hTy)
              all_goals first
                | exact eo_type_valid_of_generic_apply_eq_dtcapp_full
                    (f := Term.UOp2 op y z) (x := x) (A := a) (B := b)
                    (go (Term.UOp2 op y z))
                    (by
                      intro s d i j h
                      rcases eo_to_smt_eq_dt_sel_cases
                          (Term.UOp2 op y z) s d i j h with
                        ⟨d0, hd, hTerm, hReserved⟩ | ⟨q, hTerm, hq⟩
                      · cases hTerm
                      · cases hTerm)
                    (by
                      intro s d i h
                      exact eo_to_smt_ne_dt_tester (Term.UOp2 op y z) s d i h)
                    rfl rfl hTermNN (by
                      change
                        __eo_typeof_apply (__eo_typeof (Term.UOp2 op y z))
                            (__eo_typeof x) =
                          Term.DtcAppType a b
                      exact hTy)
                | exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
                    (by intro T U h; cases h)
                    (by intro T U h; cases h)
                    hTy
                | simp [eo_type_valid, eo_type_valid_rec, __eo_to_smt_type,
                    __eo_typeof_apply, __eo_requires,
                    __eo_typeof__at_array_deq_diff, __eo_typeof_extract,
                    __eo_typeof_re_loop,
                    __eo_typeof__at_strings_deq_diff,
                    __eo_typeof__at_strings_num_occur_re,
                    __eo_typeof__at_strings_occur_index_re,
                    __eo_typeof__at_sets_deq_diff,
                    __eo_typeof__at_quantifiers_skolemize,
                    __eo_typeof__at_const, __eo_mk_apply, __eo_add, __eo_mul,
                    __is_arith_type, __eo_eq, __eo_and, native_ite, native_teq,
                    native_not] at hTy hTypeNN ⊢
            case UOp3 op y z w =>
              first
                | exact eo_type_valid_of_generic_apply_eq_dtcapp_full
                    (f := Term.UOp3 op y z w) (x := x) (A := a) (B := b)
                    (go (Term.UOp3 op y z w))
                    (by
                      intro s d i j h
                      rcases eo_to_smt_eq_dt_sel_cases
                          (Term.UOp3 op y z w) s d i j h with
                        ⟨d0, hd, hTerm, hReserved⟩ | ⟨q, hTerm, hq⟩
                      · cases hTerm
                      · cases hTerm)
                    (by
                      intro s d i h
                      exact eo_to_smt_ne_dt_tester (Term.UOp3 op y z w) s d i h)
                    rfl rfl hTermNN hTy
                | (cases op <;> dsimp [__eo_typeof, __eo_typeof__at_re_unfold_pos_component] at hTy hTypeNN
                   all_goals first
                    | exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
                        (by intro T U h; cases h)
                        (by intro T U h; cases h)
                        hTy
                    | simp [eo_type_valid, eo_type_valid_rec, __eo_to_smt_type,
                        __eo_typeof_apply, __eo_requires,
                        __eo_typeof__at_re_unfold_pos_component, native_ite,
                        native_teq, native_not] at hTy hTypeNN ⊢)
            case Apply g y =>
              cases g <;> dsimp [__eo_typeof] at hTy hTypeNN
              case UOp op =>
                cases op <;> dsimp [__eo_typeof] at hTy hTypeNN
                case select =>
                  exact eo_type_valid_of_select_eq_dtcapp_full
                    (go y) (go x) hTermNN hTy
                case seq_nth =>
                  exact eo_type_valid_of_seq_nth_eq_dtcapp_full
                    (go y) (go x) hTermNN hTy
                case plus =>
                  exact False.elim (false_of_typeof_plus_eq_dtcapp_full hTy)
                case neg =>
                  exact False.elim (false_of_typeof_plus_eq_dtcapp_full hTy)
                case mult =>
                  exact False.elim (false_of_typeof_plus_eq_dtcapp_full hTy)
                case lt =>
                  exact False.elim (false_of_typeof_lt_eq_dtcapp_full hTy)
                case leq =>
                  exact False.elim (false_of_typeof_lt_eq_dtcapp_full hTy)
                case gt =>
                  exact False.elim (false_of_typeof_lt_eq_dtcapp_full hTy)
                case geq =>
                  exact False.elim (false_of_typeof_lt_eq_dtcapp_full hTy)
                case set_member =>
                  exact False.elim (false_of_typeof_set_member_eq_dtcapp_full hTy)
                case qdiv =>
                  exact False.elim (false_of_typeof_qdiv_eq_dtcapp_full hTy)
                case qdiv_total =>
                  exact False.elim (false_of_typeof_qdiv_eq_dtcapp_full hTy)
                case _at_array_deq_diff =>
                  have hEq :=
                    eo_to_smt_typeof_matches_translation_array_deq_diff y x
                      (fun h => (go y h).1) (fun h => (go y h).2)
                      (fun h => (go x h).1) (fun h => (go x h).2) hNonNone
                  have hValid :=
                    eo_type_valid_of_array_deq_diff_non_none_full y x hEq hNonNone
                  change
                    eo_type_valid
                      (__eo_typeof__at_array_deq_diff (__eo_typeof y) (__eo_typeof x))
                    at hValid
                  rw [hTy] at hValid
                  exact hValid
                case _at_strings_deq_diff =>
                  have hValid :=
                    (eo_to_smt_typeof_matches_translation_apply_at_strings_deq_diff
                      x y (fun h => (go y h).1) (fun h => (go x h).1)
                      hNonNone).2
                  change
                    eo_type_valid
                      (__eo_typeof__at_strings_deq_diff (__eo_typeof y) (__eo_typeof x))
                    at hValid
                  rw [hTy] at hValid
                  exact hValid
                case _at_strings_stoi_result =>
                  exact False.elim
                    (false_of_typeof_strings_stoi_result_eq_dtcapp_full hTy)
                case _at_strings_itos_result =>
                  exact False.elim
                    (false_of_typeof_strings_itos_result_eq_dtcapp_full hTy)
                case _at_strings_num_occur_re =>
                  exact False.elim
                    (false_of_typeof_strings_num_occur_re_eq_dtcapp_full (by
                      change
                        __eo_typeof__at_strings_num_occur_re
                            (__eo_typeof y) (__eo_typeof x) =
                          Term.DtcAppType a b
                      exact hTy))
                case _at_sets_deq_diff =>
                  have hEq :=
                    eo_to_smt_typeof_matches_translation_sets_deq_diff y x
                      (fun h => (go y h).1) (fun h => (go y h).2)
                      (fun h => (go x h).1) (fun h => (go x h).2) hNonNone
                  have hValid :=
                    eo_type_valid_of_sets_deq_diff_non_none_full y x hEq hNonNone
                  change
                    eo_type_valid
                      (__eo_typeof__at_sets_deq_diff (__eo_typeof y) (__eo_typeof x))
                    at hValid
                  rw [hTy] at hValid
                  exact hValid
                all_goals first
                  | exact False.elim
                      (hNonNone
                        (typeof_apply_apply_none_head_eq (__eo_to_smt y) (__eo_to_smt x)))
                  | exact eo_type_valid_of_nested_generic_apply_typeof_apply_eq_dtcapp_full
                      (go _) (by rfl) hTermNN hTy
                  | exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
                      (by intro T U h; cases h)
                      (by intro T U h; cases h)
                      hTy
                  | (simp [
                        __eo_requires,
                        
                        __eo_typeof_or,
                        __eo_typeof_eq,
                        __eo_typeof_div, __eo_typeof_divisible, __eo_typeof_concat,
                        __eo_typeof_bvand, __eo_typeof_bvcomp, __eo_typeof_bvult,
                        __eo_typeof__at_from_bools, __eo_typeof_str_concat,
                        __eo_typeof_str_contains, __eo_typeof_str_at,
                        __eo_typeof_str_lt, __eo_typeof_re_range,
                        __eo_typeof_re_concat, __eo_typeof_str_in_re,
                        __eo_typeof__at_strings_deq_diff, __eo_typeof_tuple,
                        __eo_typeof_set_union,
                        __eo_typeof_set_subset, __eo_typeof_set_insert,
                        __eo_typeof_forall,
                        
                        __eo_is_list,
                        __eo_is_ok,
                        __eo_list_len, __eo_eq,
                        __eo_mk_apply, __eo_add, native_ite, native_teq,
                        native_not] at hTy hTypeNN
                     repeat (first | split at hTy | split at hTypeNN)
                     all_goals simp [eo_type_valid
                       
                       
                       
                       
                       ] at hTy hTypeNN ⊢
                     all_goals
                       repeat (first | split at hTy | split at hTypeNN)
                     all_goals simp at hTy hTypeNN ⊢
                     all_goals
                       try
                         (cases hy : __eo_typeof y <;> cases hx : __eo_typeof x <;>
                          simp [hy, hx,
                            __eo_to_smt_type
                            
                            
                            
                            ] at hTy hTypeNN ⊢)
                     all_goals
                       repeat (first | split at hTy | split at hTypeNN)
                     all_goals simp at hTy hTypeNN ⊢
                     all_goals cases hTy)
                  | (set_option linter.unusedSimpArgs false in
                     simp [eo_type_valid, eo_type_valid_rec, __eo_to_smt_type,
                       __eo_typeof_apply, __eo_requires, __eo_typeof__at__at_Pair,
                       __eo_typeof__at__at_pair, __eo_typeof__at__at_TypedList_cons,
                       __eo_typeof_or, __eo_typeof_eq, __eo_typeof_plus,
                       __eo_typeof_lt, __eo_typeof_div, __eo_typeof_divisible,
                       __eo_typeof_concat, __eo_typeof_bvand, __eo_typeof_bvcomp,
                       __eo_typeof_bvult, __eo_typeof__at_from_bools,
                       __eo_typeof_str_concat, __eo_typeof_str_contains,
                       __eo_typeof_str_at, __eo_typeof_str_lt,
                       __eo_typeof_re_range, __eo_typeof_re_concat,
                       __eo_typeof_str_in_re, __eo_typeof__at_strings_deq_diff,
                       __eo_typeof_tuple, __eo_typeof_set_union,
                       __eo_typeof_set_member, __eo_typeof_set_subset,
                       __eo_typeof_set_insert, __eo_typeof_qdiv,
                       __eo_typeof_forall, __eo_is_list, __eo_get_nil_rec,
                       __eo_is_list_nil, __eo_is_ok, __eo_list_len, __is_arith_type,
                       __eo_eq, __eo_and, __eo_mk_apply, __eo_add, native_ite,
                       native_teq, native_not] at hTy hTypeNN ⊢
                     all_goals
                       cases hy : __eo_typeof y <;> cases hx : __eo_typeof x <;>
                         simp [hy, hx, eo_type_valid, eo_type_valid_rec,
                           __eo_to_smt_type, __eo_requires, native_ite,
                           native_teq, native_not] at hTy hTypeNN ⊢
                     all_goals
                       repeat (first | split at hTy | split at hTypeNN)
                     all_goals
                       simp_all [eo_type_valid, eo_type_valid_rec,
                         __eo_to_smt_type, __eo_requires, native_ite,
                         native_teq, native_not]
                     all_goals cases hTy)
              case UOp1 op z =>
                cases op <;> dsimp [__eo_typeof] at hTy hTypeNN
                case «repeat» =>
                  exact eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
                    (g := Term.UOp1 UserOp1.repeat z) (y := y) (x := x)
                    (A := a) (B := b)
                    (go (Term.Apply (Term.UOp1 UserOp1.repeat z) y))
                    (by rfl) (by rfl) hTermNN (by
                      change
                        __eo_typeof
                            (Term.Apply (Term.Apply (Term.UOp1 UserOp1.repeat z) y) x) =
                          Term.DtcAppType a b
                      exact hTy)
                case zero_extend =>
                  exact eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
                    (g := Term.UOp1 UserOp1.zero_extend z) (y := y) (x := x)
                    (A := a) (B := b)
                    (go (Term.Apply (Term.UOp1 UserOp1.zero_extend z) y))
                    (by rfl) (by rfl) hTermNN (by
                      change
                        __eo_typeof
                            (Term.Apply (Term.Apply (Term.UOp1 UserOp1.zero_extend z) y) x) =
                          Term.DtcAppType a b
                      exact hTy)
                case sign_extend =>
                  exact eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
                    (g := Term.UOp1 UserOp1.sign_extend z) (y := y) (x := x)
                    (A := a) (B := b)
                    (go (Term.Apply (Term.UOp1 UserOp1.sign_extend z) y))
                    (by rfl) (by rfl) hTermNN (by
                      change
                        __eo_typeof
                            (Term.Apply (Term.Apply (Term.UOp1 UserOp1.sign_extend z) y) x) =
                          Term.DtcAppType a b
                      exact hTy)
                case rotate_left =>
                  exact eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
                    (g := Term.UOp1 UserOp1.rotate_left z) (y := y) (x := x)
                    (A := a) (B := b)
                    (go (Term.Apply (Term.UOp1 UserOp1.rotate_left z) y))
                    (by rfl) (by rfl) hTermNN (by
                      change
                        __eo_typeof
                            (Term.Apply (Term.Apply (Term.UOp1 UserOp1.rotate_left z) y) x) =
                          Term.DtcAppType a b
                      exact hTy)
                case rotate_right =>
                  exact eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
                    (g := Term.UOp1 UserOp1.rotate_right z) (y := y) (x := x)
                    (A := a) (B := b)
                    (go (Term.Apply (Term.UOp1 UserOp1.rotate_right z) y))
                    (by rfl) (by rfl) hTermNN (by
                      change
                        __eo_typeof
                            (Term.Apply (Term.Apply (Term.UOp1 UserOp1.rotate_right z) y) x) =
                          Term.DtcAppType a b
                      exact hTy)
                case _at_bit =>
                  exact eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
                    (g := Term.UOp1 UserOp1._at_bit z) (y := y) (x := x)
                    (A := a) (B := b)
                    (go (Term.Apply (Term.UOp1 UserOp1._at_bit z) y))
                    (by rfl) (by rfl) hTermNN (by
                      change
                        __eo_typeof
                            (Term.Apply (Term.Apply (Term.UOp1 UserOp1._at_bit z) y) x) =
                          Term.DtcAppType a b
                      exact hTy)
                case seq_empty =>
                  exact eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
                    (g := Term.UOp1 UserOp1.seq_empty z) (y := y) (x := x)
                    (A := a) (B := b)
                    (go (Term.Apply (Term.UOp1 UserOp1.seq_empty z) y))
                    (by rfl) (by rfl) hTermNN (by
                      change
                        __eo_typeof
                            (Term.Apply (Term.Apply (Term.UOp1 UserOp1.seq_empty z) y) x) =
                          Term.DtcAppType a b
                      exact hTy)
                case re_exp =>
                  exact eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
                    (g := Term.UOp1 UserOp1.re_exp z) (y := y) (x := x)
                    (A := a) (B := b)
                    (go (Term.Apply (Term.UOp1 UserOp1.re_exp z) y))
                    (by rfl) (by rfl) hTermNN (by
                      change
                        __eo_typeof
                            (Term.Apply (Term.Apply (Term.UOp1 UserOp1.re_exp z) y) x) =
                          Term.DtcAppType a b
                      exact hTy)
                case «is» =>
                  exact eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
                    (g := Term.UOp1 UserOp1.is z) (y := y) (x := x)
                    (A := a) (B := b)
                    (go (Term.Apply (Term.UOp1 UserOp1.is z) y))
                    (by rfl) (by rfl) hTermNN (by
                      change
                        __eo_typeof
                            (Term.Apply (Term.Apply (Term.UOp1 UserOp1.is z) y) x) =
                          Term.DtcAppType a b
                      exact hTy)
                case update =>
                  cases hz : __eo_to_smt z
                  case DtSel s d i j =>
                    have hUpdaterNN :
                        __smtx_typeof
                            (__eo_to_smt_updater (SmtTerm.DtSel s d i j)
                              (__eo_to_smt y) (__eo_to_smt x)) ≠
                          SmtType.None := by
                      change
                        __smtx_typeof
                            (__eo_to_smt_updater (__eo_to_smt z)
                              (__eo_to_smt y) (__eo_to_smt x)) ≠
                          SmtType.None at hNonNone
                      rw [hz] at hNonNone
                      exact hNonNone
                    have hIdx :
                        native_zlt (native_nat_to_int j)
                            (native_nat_to_int
                              (__smtx_dt_num_sels (__smtx_dd_lookup s d) i)) =
                          true :=
                      eo_to_smt_updater_dt_sel_guard_of_non_none
                        s d i j (__eo_to_smt y) (__eo_to_smt x) hUpdaterNN
                    have hIteNN :
                        term_has_non_none_type
                          (SmtTerm.ite
                            (SmtTerm.Apply (SmtTerm.DtTester s d i) (__eo_to_smt y))
                            (__eo_to_smt_updater_rec
                              (SmtTerm.DtSel s d i j)
                              (__smtx_dt_num_sels (__smtx_dd_lookup s d) i)
                              (__eo_to_smt y) (__eo_to_smt x)
                              (SmtTerm.DtCons s d i))
                            (__eo_to_smt y)) := by
                      unfold term_has_non_none_type
                      simpa [__eo_to_smt_updater, native_ite, hIdx] using hUpdaterNN
                    rcases ite_args_of_non_none hIteNN with
                      ⟨T, hCond, _hThen, hElse, _hT⟩
                    have hCondNN :
                        term_has_non_none_type
                          (SmtTerm.Apply (SmtTerm.DtTester s d i) (__eo_to_smt y)) := by
                      unfold term_has_non_none_type
                      rw [hCond]
                      simp
                    have hYTy :
                        __smtx_typeof (__eo_to_smt y) = SmtType.Datatype s d :=
                      dt_tester_arg_datatype_of_non_none hCondNN
                    have hYNN : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
                      rw [hYTy]
                      simp
                    have hYValid : eo_type_valid (__eo_typeof y) := (go y hYNN).2
                    exact eo_type_valid_of_update_eq_dtcapp_full hYValid (by
                      change
                        __eo_typeof_update (__eo_typeof z) (__eo_typeof y)
                            (__eo_typeof x) =
                          Term.DtcAppType a b
                      exact hTy)
                  all_goals
                    exact False.elim (hNonNone (by
                      change
                        __smtx_typeof
                            (__eo_to_smt_updater (__eo_to_smt z)
                              (__eo_to_smt y) (__eo_to_smt x)) =
                          SmtType.None
                      rw [hz]
                      simp [__eo_to_smt_updater]))
                case tuple_select =>
                  exact eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
                    (g := Term.UOp1 UserOp1.tuple_select z) (y := y) (x := x)
                    (A := a) (B := b)
                    (go (Term.Apply (Term.UOp1 UserOp1.tuple_select z) y))
                    (by rfl) (by rfl) hTermNN (by
                      change
                        __eo_typeof
                            (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_select z) y) x) =
                          Term.DtcAppType a b
                      exact hTy)
                case tuple_update =>
                  cases hYType : __smtx_typeof (__eo_to_smt y)
                  case Datatype s d =>
                    cases hz : __eo_to_smt z
                    case Numeral n =>
                      by_cases hs : s = (native_string_lit "@Tuple")
                      · subst s
                        have hTupleNN :
                            __smtx_typeof
                                (__eo_to_smt_tuple_update (SmtType.Datatype (native_string_lit "@Tuple") d)
                                  (SmtTerm.Numeral n) (__eo_to_smt y) (__eo_to_smt x)) ≠
                              SmtType.None := by
                          change
                            __smtx_typeof
                                (__eo_to_smt_tuple_update
                                  (__smtx_typeof (__eo_to_smt y)) (__eo_to_smt z)
                                  (__eo_to_smt y) (__eo_to_smt x)) ≠
                              SmtType.None at hNonNone
                          rw [hYType, hz] at hNonNone
                          exact hNonNone
                        have hDecl :
                            ∃ body, d = __eo_to_smt_tuple_decl body := by
                          cases d with
                          | nil =>
                              exfalso
                              apply hTupleNN
                              simp [__eo_to_smt_tuple_update]
                          | cons s2 body rest =>
                              cases rest with
                              | nil =>
                                  by_cases hs2 :
                                      s2 = native_string_lit "@Tuple"
                                  · subst s2
                                    exact ⟨body, rfl⟩
                                  · exfalso
                                    apply hTupleNN
                                    simp [__eo_to_smt_tuple_update, hs2,
                                      native_streq, native_and, native_ite]
                              | cons s3 body3 rest3 =>
                                  exfalso
                                  apply hTupleNN
                                  simp [__eo_to_smt_tuple_update]
                        rcases hDecl with ⟨body, rfl⟩
                        let tupleDD := __eo_to_smt_tuple_decl body
                        have hGe : native_zleq 0 n = true := by
                          cases hTest : native_zleq 0 n
                          · simp [__eo_to_smt_tuple_update,
                              __eo_to_smt_tuple_decl, hTest,
                              native_streq, native_and, native_ite] at hTupleNN
                          · rfl
                        have hUpdaterNN :
                            __smtx_typeof
                                (__eo_to_smt_updater
                                  (SmtTerm.DtSel (native_string_lit "@Tuple") tupleDD native_nat_zero
                                    (native_int_to_nat n))
                                  (__eo_to_smt y) (__eo_to_smt x)) ≠
                              SmtType.None := by
                          simpa [__eo_to_smt_tuple_update,
                            __eo_to_smt_tuple_decl, tupleDD, hGe,
                            native_streq, native_and, native_ite] using
                            hTupleNN
                        have hIdx :
                            native_zlt
                                (native_nat_to_int (native_int_to_nat n))
                                (native_nat_to_int
                                  (__smtx_dt_num_sels
                                    (__smtx_dd_lookup
                                      (native_string_lit "@Tuple") tupleDD)
                                    native_nat_zero)) =
                              true :=
                          eo_to_smt_updater_dt_sel_guard_of_non_none
                            (native_string_lit "@Tuple") tupleDD native_nat_zero
                            (native_int_to_nat n)
                            (__eo_to_smt y) (__eo_to_smt x) hUpdaterNN
                        have hIteNN :
                            term_has_non_none_type
                              (SmtTerm.ite
                                  (SmtTerm.Apply
                                  (SmtTerm.DtTester (native_string_lit "@Tuple") tupleDD native_nat_zero)
                                  (__eo_to_smt y))
                                (__eo_to_smt_updater_rec
                                  (SmtTerm.DtSel (native_string_lit "@Tuple") tupleDD native_nat_zero
                                    (native_int_to_nat n))
                                  (__smtx_dt_num_sels
                                    (__smtx_dd_lookup
                                      (native_string_lit "@Tuple") tupleDD)
                                    native_nat_zero)
                                  (__eo_to_smt y) (__eo_to_smt x)
                                  (SmtTerm.DtCons (native_string_lit "@Tuple") tupleDD native_nat_zero))
                                (__eo_to_smt y)) := by
                          unfold term_has_non_none_type
                          simpa [__eo_to_smt_updater, native_ite, hIdx] using hUpdaterNN
                        rcases ite_args_of_non_none hIteNN with
                          ⟨T, hCond, _hThen, hElse, _hT⟩
                        have hCondNN :
                            term_has_non_none_type
                              (SmtTerm.Apply
                                (SmtTerm.DtTester (native_string_lit "@Tuple") tupleDD native_nat_zero)
                                (__eo_to_smt y)) := by
                          unfold term_has_non_none_type
                          rw [hCond]
                          simp
                        have hYTy :
                            __smtx_typeof (__eo_to_smt y) =
                              SmtType.Datatype (native_string_lit "@Tuple") tupleDD :=
                          dt_tester_arg_datatype_of_non_none hCondNN
                        have hYNN : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
                          rw [hYTy]
                          simp
                        have hYValid : eo_type_valid (__eo_typeof y) := (go y hYNN).2
                        exact eo_type_valid_of_tuple_update_eq_dtcapp_full hYValid (by
                          change
                            __eo_typeof_tuple_update
                                (__eo_typeof z) z (__eo_typeof y) (__eo_typeof x) =
                              Term.DtcAppType a b
                          exact hTy)
                      · exact False.elim (hNonNone (by
                          change
                            __smtx_typeof
                                (__eo_to_smt_tuple_update
                                  (__smtx_typeof (__eo_to_smt y)) (__eo_to_smt z)
                                  (__eo_to_smt y) (__eo_to_smt x)) =
                              SmtType.None
                          rw [hYType, hz]
                          cases d with
                          | nil =>
                              simp [__eo_to_smt_tuple_update]
                          | cons s2 body rest =>
                              cases rest with
                              | nil =>
                                  simp [__eo_to_smt_tuple_update, hs,
                                    native_streq, native_and, native_ite]
                              | cons s3 body3 rest3 =>
                                  simp [__eo_to_smt_tuple_update]))
                    all_goals
                      exact False.elim (hNonNone (by
                        change
                          __smtx_typeof
                              (__eo_to_smt_tuple_update
                                (__smtx_typeof (__eo_to_smt y)) (__eo_to_smt z)
                                (__eo_to_smt y) (__eo_to_smt x)) =
                            SmtType.None
                        rw [hYType, hz]
                        simp [__eo_to_smt_tuple_update]))
                  all_goals
                    exact False.elim (hNonNone (by
                      change
                        __smtx_typeof
                            (__eo_to_smt_tuple_update
                              (__smtx_typeof (__eo_to_smt y)) (__eo_to_smt z)
                              (__eo_to_smt y) (__eo_to_smt x)) =
                          SmtType.None
                      rw [hYType]
                      simp [__eo_to_smt_tuple_update]))
                case set_empty =>
                  exact eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
                    (g := Term.UOp1 UserOp1.set_empty z) (y := y) (x := x)
                    (A := a) (B := b)
                    (go (Term.Apply (Term.UOp1 UserOp1.set_empty z) y))
                    (by rfl) (by rfl) hTermNN (by
                      change
                        __eo_typeof
                            (Term.Apply (Term.Apply (Term.UOp1 UserOp1.set_empty z) y) x) =
                          Term.DtcAppType a b
                      exact hTy)
                case int_to_bv =>
                  exact eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
                    (g := Term.UOp1 UserOp1.int_to_bv z) (y := y) (x := x)
                    (A := a) (B := b)
                    (go (Term.Apply (Term.UOp1 UserOp1.int_to_bv z) y))
                    (by rfl) (by rfl) hTermNN (by
                      change
                        __eo_typeof
                            (Term.Apply (Term.Apply (Term.UOp1 UserOp1.int_to_bv z) y) x) =
                          Term.DtcAppType a b
                      exact hTy)
                all_goals first
                  | exact eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
                      (g := Term.UOp1 op z) (y := y) (x := x) (A := a) (B := b)
                      (go (Term.Apply (Term.UOp1 op z) y))
                      (by rfl) (by rfl) hTermNN hTy
                  | exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
                      (by intro T U h; cases h)
                      (by intro T U h; cases h)
                      (by
                        simpa [__eo_typeof] using hTy)
                  | simp [eo_type_valid, eo_type_valid_rec, __eo_to_smt_type,
                      __eo_typeof_apply, __eo_requires,
                      __eo_typeof__at_witness_string_length, __eo_typeof_update,
                      __eo_typeof_tuple_update, __eo_requires, __eo_eq,
                      native_ite, native_teq, native_not] at hTy hTypeNN ⊢
              case UOp2 op z w =>
                exact eo_type_valid_of_nested_generic_apply_typeof_apply_eq_dtcapp_full
                  (g := Term.UOp2 op z w) (y := y) (x := x) (A := a) (B := b)
                  (go (Term.Apply (Term.UOp2 op z w) y))
                  (by rfl) hTermNN hTy
              case UOp3 op z w v =>
                exact eo_type_valid_of_nested_generic_apply_typeof_apply_eq_dtcapp_full
                  (g := Term.UOp3 op z w v) (y := y) (x := x) (A := a) (B := b)
                  (go (Term.Apply (Term.UOp3 op z w v) y))
                  (by rfl) hTermNN hTy
              case Apply g0 z =>
                by_cases hG0UOp : ∃ op, g0 = Term.UOp op
                · rcases hG0UOp with ⟨op, rfl⟩
                  by_cases hIte : op = UserOp.ite
                  · subst op
                    have hIteNN :
                        term_has_non_none_type
                          (SmtTerm.ite (__eo_to_smt z) (__eo_to_smt y)
                            (__eo_to_smt x)) := by
                      change
                        term_has_non_none_type
                          (SmtTerm.ite (__eo_to_smt z) (__eo_to_smt y)
                            (__eo_to_smt x)) at hTermNN
                      exact hTermNN
                    rcases ite_args_of_non_none hIteNN with
                      ⟨T, _hCond, hThen, _hElse, hTNN⟩
                    have hYNN : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
                      rw [hThen]
                      exact hTNN
                    have hYValid : eo_type_valid (__eo_typeof y) := (go y hYNN).2
                    exact eo_type_valid_of_ite_eq_dtcapp_full hYValid (by
                      change
                        __eo_typeof_ite (__eo_typeof z) (__eo_typeof y)
                            (__eo_typeof x) =
                          Term.DtcAppType a b
                      exact hTy)
                  by_cases hStore : op = UserOp.store
                  · subst op
                    exact False.elim (false_of_typeof_store_eq_dtcapp_full (by
                      change
                        __eo_typeof_store (__eo_typeof z) (__eo_typeof y)
                            (__eo_typeof x) =
                          Term.DtcAppType a b
                      exact hTy))
                  by_cases hBvite : op = UserOp.bvite
                  · subst op
                    have hIteNN :
                        term_has_non_none_type
                          (SmtTerm.ite
                            (SmtTerm.eq (__eo_to_smt z) (SmtTerm.Binary 1 1))
                            (__eo_to_smt y) (__eo_to_smt x)) := by
                      change
                        term_has_non_none_type
                          (SmtTerm.ite
                            (SmtTerm.eq (__eo_to_smt z) (SmtTerm.Binary 1 1))
                            (__eo_to_smt y) (__eo_to_smt x)) at hTermNN
                      exact hTermNN
                    rcases ite_args_of_non_none hIteNN with
                      ⟨T, _hCond, hThen, _hElse, hTNN⟩
                    have hYNN : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
                      rw [hThen]
                      exact hTNN
                    have hYValid : eo_type_valid (__eo_typeof y) := (go y hYNN).2
                    exact eo_type_valid_of_bvite_eq_dtcapp_full hYValid (by
                      change
                        __eo_typeof_bvite (__eo_typeof z) (__eo_typeof y)
                            (__eo_typeof x) =
                          Term.DtcAppType a b
                      exact hTy)
                  by_cases hStrSubstr : op = UserOp.str_substr
                  · subst op
                    exact False.elim
                      (false_of_typeof_str_substr_eq_dtcapp_full (by
                        change
                          __eo_typeof_str_substr (__eo_typeof z)
                              (__eo_typeof y) (__eo_typeof x) =
                            Term.DtcAppType a b
                        exact hTy))
                  by_cases hStrReplace : op = UserOp.str_replace
                  · subst op
                    exact False.elim
                      (false_of_typeof_str_replace_eq_dtcapp_full (by
                        change
                          __eo_typeof_str_replace (__eo_typeof z)
                              (__eo_typeof y) (__eo_typeof x) =
                            Term.DtcAppType a b
                        exact hTy))
                  by_cases hStrIndexof : op = UserOp.str_indexof
                  · subst op
                    exact False.elim
                      (false_of_typeof_str_indexof_eq_dtcapp_full (by
                        change
                          __eo_typeof_str_indexof (__eo_typeof z)
                              (__eo_typeof y) (__eo_typeof x) =
                            Term.DtcAppType a b
                        exact hTy))
                  by_cases hStrUpdate : op = UserOp.str_update
                  · subst op
                    exact False.elim
                      (false_of_typeof_str_update_eq_dtcapp_full (by
                        change
                          __eo_typeof_str_update (__eo_typeof z)
                              (__eo_typeof y) (__eo_typeof x) =
                            Term.DtcAppType a b
                        exact hTy))
                  by_cases hStrReplaceAll : op = UserOp.str_replace_all
                  · subst op
                    exact False.elim
                      (false_of_typeof_str_replace_eq_dtcapp_full (by
                        change
                          __eo_typeof_str_replace (__eo_typeof z)
                              (__eo_typeof y) (__eo_typeof x) =
                            Term.DtcAppType a b
                        exact hTy))
                  by_cases hStrReplaceRe : op = UserOp.str_replace_re
                  · subst op
                    exact False.elim
                      (false_of_typeof_str_replace_re_eq_dtcapp_full (by
                        change
                          __eo_typeof_str_replace_re (__eo_typeof z)
                              (__eo_typeof y) (__eo_typeof x) =
                            Term.DtcAppType a b
                        exact hTy))
                  by_cases hStrReplaceReAll : op = UserOp.str_replace_re_all
                  · subst op
                    exact False.elim
                      (false_of_typeof_str_replace_re_eq_dtcapp_full (by
                        change
                          __eo_typeof_str_replace_re (__eo_typeof z)
                              (__eo_typeof y) (__eo_typeof x) =
                            Term.DtcAppType a b
                        exact hTy))
                  by_cases hStrIndexofRe : op = UserOp.str_indexof_re
                  · subst op
                    exact False.elim
                      (false_of_typeof_str_indexof_re_eq_dtcapp_full (by
                        change
                          __eo_typeof_str_indexof_re (__eo_typeof z)
                              (__eo_typeof y) (__eo_typeof x) =
                            Term.DtcAppType a b
                        exact hTy))
                  by_cases hStringsOccurIndex :
                      op = UserOp._at_strings_occur_index
                  · subst op
                    exact False.elim
                      (false_of_typeof_str_indexof_eq_dtcapp_full (by
                        change
                          __eo_typeof_str_indexof (__eo_typeof z)
                              (__eo_typeof y) (__eo_typeof x) =
                            Term.DtcAppType a b
                        exact hTy))
                  by_cases hStringsOccurIndexRe :
                      op = UserOp._at_strings_occur_index_re
                  · subst op
                    exact False.elim
                      (false_of_typeof_str_indexof_re_eq_dtcapp_full (by
                        change
                          __eo_typeof_str_indexof_re (__eo_typeof z)
                              (__eo_typeof y) (__eo_typeof x) =
                            Term.DtcAppType a b
                        exact hTy))
                  exact eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
                    (g := Term.Apply (Term.UOp op) z) (y := y) (x := x)
                    (A := a) (B := b)
                    (go (Term.Apply (Term.Apply (Term.UOp op) z) y))
                    (eo_to_smt_apply_apply_apply_uop_generic_full op z y x
                      hIte hStore hBvite hStrSubstr hStrReplace hStrIndexof
                      hStrUpdate hStrReplaceAll hStrReplaceRe hStrReplaceReAll
                      hStrIndexofRe hStringsOccurIndex
                      hStringsOccurIndexRe)
                    (eo_typeof_apply_apply_apply_uop_generic_full op z y x
                      hIte hStore hBvite hStrSubstr hStrReplace hStrIndexof
                      hStrUpdate hStrReplaceAll hStrReplaceRe hStrReplaceReAll
                      hStrIndexofRe hStringsOccurIndex
                      hStringsOccurIndexRe)
                    hTermNN hTy
                ·
                  exact eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
                    (g := Term.Apply g0 z) (y := y) (x := x) (A := a) (B := b)
                    (go (Term.Apply (Term.Apply g0 z) y))
                    (by
                      cases g0 <;> try rfl
                      case UOp op =>
                        exact False.elim (hG0UOp ⟨op, rfl⟩)
                      case Apply g1 w =>
                        cases g1 <;> try rfl
                        case UOp op =>
                          cases op <;> try rfl
                          case _at_strings_replace_all_result =>
                            exact False.elim
                              (false_of_typeof_strings_replace_all_result_eq_dtcapp_full
                                (by
                                  change
                                    __eo_typeof__at_strings_replace_all_result
                                        (__eo_typeof w) (__eo_typeof z)
                                        (__eo_typeof y) (__eo_typeof x) =
                                      Term.DtcAppType a b
                                  exact hTy))
                          case _at_strings_replace_re_all_result =>
                            exact False.elim
                              (false_of_typeof_strings_replace_re_all_result_eq_dtcapp_full
                                (by
                                  change
                                    __eo_typeof__at_strings_replace_re_all_result
                                        (__eo_typeof w) (__eo_typeof z)
                                        (__eo_typeof y) (__eo_typeof x) =
                                      Term.DtcAppType a b
                                  exact hTy)))
                    (by
                      cases g0 <;> try rfl
                      case UOp op =>
                        exact False.elim (hG0UOp ⟨op, rfl⟩)
                      case Apply g1 w =>
                        cases g1 <;> try rfl
                        case UOp op =>
                          cases op <;> try rfl
                          case _at_strings_replace_all_result =>
                            exact False.elim
                              (false_of_typeof_strings_replace_all_result_eq_dtcapp_full
                                (by
                                  change
                                    __eo_typeof__at_strings_replace_all_result
                                        (__eo_typeof w) (__eo_typeof z)
                                        (__eo_typeof y) (__eo_typeof x) =
                                      Term.DtcAppType a b
                                  exact hTy))
                          case _at_strings_replace_re_all_result =>
                            exact False.elim
                              (false_of_typeof_strings_replace_re_all_result_eq_dtcapp_full
                                (by
                                  change
                                    __eo_typeof__at_strings_replace_re_all_result
                                        (__eo_typeof w) (__eo_typeof z)
                                        (__eo_typeof y) (__eo_typeof x) =
                                      Term.DtcAppType a b
                                  exact hTy)))
                    hTermNN hTy
              case __eo_List =>
                exact eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
                  (g := Term.__eo_List) (y := y) (x := x) (A := a) (B := b)
                  (go (Term.Apply Term.__eo_List y))
                  (by rfl) (by rfl) hTermNN (by
                    change
                      __eo_typeof (Term.Apply (Term.Apply Term.__eo_List y) x) =
                        Term.DtcAppType a b
                    exact hTy)
              case __eo_List_nil =>
                exact eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
                  (g := Term.__eo_List_nil) (y := y) (x := x) (A := a) (B := b)
                  (go (Term.Apply Term.__eo_List_nil y))
                  (by rfl) (by rfl) hTermNN (by
                    change
                      __eo_typeof (Term.Apply (Term.Apply Term.__eo_List_nil y) x) =
                        Term.DtcAppType a b
                    exact hTy)
              case Bool =>
                exact eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
                  (g := Term.Bool) (y := y) (x := x) (A := a) (B := b)
                  (go (Term.Apply Term.Bool y))
                  (by rfl) (by rfl) hTermNN (by
                    change
                      __eo_typeof (Term.Apply (Term.Apply Term.Bool y) x) =
                        Term.DtcAppType a b
                    exact hTy)
              case Boolean q =>
                exact eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
                  (g := Term.Boolean q) (y := y) (x := x) (A := a) (B := b)
                  (go (Term.Apply (Term.Boolean q) y))
                  (by rfl) (by rfl) hTermNN (by
                    change
                      __eo_typeof (Term.Apply (Term.Apply (Term.Boolean q) y) x) =
                        Term.DtcAppType a b
                    exact hTy)
              case Numeral n =>
                exact eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
                  (g := Term.Numeral n) (y := y) (x := x) (A := a) (B := b)
                  (go (Term.Apply (Term.Numeral n) y))
                  (by rfl) (by rfl) hTermNN (by
                    change
                      __eo_typeof (Term.Apply (Term.Apply (Term.Numeral n) y) x) =
                        Term.DtcAppType a b
                    exact hTy)
              case Rational q =>
                exact eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
                  (g := Term.Rational q) (y := y) (x := x) (A := a) (B := b)
                  (go (Term.Apply (Term.Rational q) y))
                  (by rfl) (by rfl) hTermNN (by
                    change
                      __eo_typeof (Term.Apply (Term.Apply (Term.Rational q) y) x) =
                        Term.DtcAppType a b
                    exact hTy)
              case String s =>
                exact eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
                  (g := Term.String s) (y := y) (x := x) (A := a) (B := b)
                  (go (Term.Apply (Term.String s) y))
                  (by rfl) (by rfl) hTermNN (by
                    change
                      __eo_typeof (Term.Apply (Term.Apply (Term.String s) y) x) =
                        Term.DtcAppType a b
                    exact hTy)
              case Binary w n =>
                exact eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
                  (g := Term.Binary w n) (y := y) (x := x) (A := a) (B := b)
                  (go (Term.Apply (Term.Binary w n) y))
                  (by rfl) (by rfl) hTermNN (by
                    change
                      __eo_typeof (Term.Apply (Term.Apply (Term.Binary w n) y) x) =
                        Term.DtcAppType a b
                    exact hTy)
              case «Type» =>
                exact eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
                  (g := Term.Type) (y := y) (x := x) (A := a) (B := b)
                  (go (Term.Apply Term.Type y))
                  (by rfl) (by rfl) hTermNN (by
                    change
                      __eo_typeof (Term.Apply (Term.Apply Term.Type y) x) =
                        Term.DtcAppType a b
                    exact hTy)
              case Stuck =>
                exact eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
                  (g := Term.Stuck) (y := y) (x := x) (A := a) (B := b)
                  (go (Term.Apply Term.Stuck y))
                  (by rfl) (by rfl) hTermNN (by
                    change
                      __eo_typeof (Term.Apply (Term.Apply Term.Stuck y) x) =
                        Term.DtcAppType a b
                    exact hTy)
              case Var name T =>
                exact eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
                  (g := Term.Var name T) (y := y) (x := x) (A := a) (B := b)
                  (go (Term.Apply (Term.Var name T) y))
                  (by rfl) (by rfl) hTermNN (by
                    change
                      __eo_typeof (Term.Apply (Term.Apply (Term.Var name T) y) x) =
                        Term.DtcAppType a b
                    exact hTy)
              case DatatypeType s d =>
                exact eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
                  (g := Term.DatatypeType s d) (y := y) (x := x) (A := a) (B := b)
                  (go (Term.Apply (Term.DatatypeType s d) y))
                  (by rfl) (by rfl) hTermNN (by
                    change
                      __eo_typeof (Term.Apply (Term.Apply (Term.DatatypeType s d) y) x) =
                        Term.DtcAppType a b
                    exact hTy)
              case DatatypeTypeRef s =>
                exact eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
                  (g := Term.DatatypeTypeRef s) (y := y) (x := x) (A := a) (B := b)
                  (go (Term.Apply (Term.DatatypeTypeRef s) y))
                  (by rfl) (by rfl) hTermNN (by
                    change
                      __eo_typeof (Term.Apply (Term.Apply (Term.DatatypeTypeRef s) y) x) =
                        Term.DtcAppType a b
                    exact hTy)
              case DtcAppType T U =>
                exact eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
                  (g := Term.DtcAppType T U) (y := y) (x := x) (A := a) (B := b)
                  (go (Term.Apply (Term.DtcAppType T U) y))
                  (by rfl) (by rfl) hTermNN (by
                    change
                      __eo_typeof (Term.Apply (Term.Apply (Term.DtcAppType T U) y) x) =
                        Term.DtcAppType a b
                    exact hTy)
              case DtCons s d i =>
                exact eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
                  (g := Term.DtCons s d i) (y := y) (x := x) (A := a) (B := b)
                  (go (Term.Apply (Term.DtCons s d i) y))
                  (by rfl) (by rfl) hTermNN (by
                    change
                      __eo_typeof (Term.Apply (Term.Apply (Term.DtCons s d i) y) x) =
                        Term.DtcAppType a b
                    exact hTy)
              case DtSel s d i j =>
                exact eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
                  (g := Term.DtSel s d i j) (y := y) (x := x) (A := a) (B := b)
                  (go (Term.Apply (Term.DtSel s d i j) y))
                  (by rfl) (by rfl) hTermNN (by
                    change
                      __eo_typeof (Term.Apply (Term.Apply (Term.DtSel s d i j) y) x) =
                        Term.DtcAppType a b
                    exact hTy)
              case USort i =>
                exact eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
                  (g := Term.USort i) (y := y) (x := x) (A := a) (B := b)
                  (go (Term.Apply (Term.USort i) y))
                  (by rfl) (by rfl) hTermNN (by
                    change
                      __eo_typeof (Term.Apply (Term.Apply (Term.USort i) y) x) =
                        Term.DtcAppType a b
                    exact hTy)
              case UConst i T =>
                exact eo_type_valid_of_nested_generic_apply_eq_dtcapp_full
                  (g := Term.UConst i T) (y := y) (x := x) (A := a) (B := b)
                  (go (Term.Apply (Term.UConst i T) y))
                  (by rfl) (by rfl) hTermNN (by
                    change
                      __eo_typeof (Term.Apply (Term.Apply (Term.UConst i T) y) x) =
                        Term.DtcAppType a b
                    exact hTy)
              case FunType =>
                cases hy : __eo_typeof y <;> cases hx : __eo_typeof x <;>
                  simp [__eo_typeof_fun_type, hy, hx] at hTy
              all_goals first
                | exact eo_type_valid_of_generic_apply_eq_dtcapp_full
                    (f := Term.Apply g y) (x := x) (A := a) (B := b)
                    (go (Term.Apply g y))
                    (by
                      intro s d i j h
                      exact (eo_to_smt_apply_ne_dt_sel g y s d i j h).elim)
                    (by
                      intro s d i h
                      exact (eo_to_smt_apply_ne_dt_tester g y s d i h).elim)
                    (by rfl) (by rfl) hTermNN (by
                      change
                        __eo_typeof (Term.Apply (Term.Apply g y) x) =
                          Term.DtcAppType a b
                      exact hTy)
                | exact eo_type_valid_of_typeof_apply_eq_dtcapp_cond_cases_full
                    (by intro T U h hU; cases h <;> cases hU)
                    (by intro T U h hU; cases h <;> cases hU)
                    hTy
                | simp [eo_type_valid, eo_type_valid_rec, __eo_to_smt_type,
                    __eo_typeof_apply, __eo_requires, native_ite, native_teq,
                    native_not] at hTy hTypeNN ⊢
            case __eo_List =>
              exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
                (by intro T U h; cases h)
                (by intro T U h; cases h)
                hTy
            case __eo_List_nil =>
              exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
                (by intro T U h; cases h)
                (by intro T U h; cases h)
                hTy
            case Bool =>
              exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
                (by intro T U h; cases h)
                (by intro T U h; cases h)
                hTy
            case Boolean =>
              exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
                (by intro T U h; cases h)
                (by intro T U h; cases h)
                hTy
            case Numeral =>
              exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
                (by intro T U h; cases h)
                (by intro T U h; cases h)
                hTy
            case Rational =>
              exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
                (by intro T U h; cases h)
                (by intro T U h; cases h)
                hTy
            case String =>
              exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
                (by intro T U h; cases h)
                (by intro T U h; cases h)
                hTy
            case Binary =>
              exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
                (by intro T U h; cases h)
                (by intro T U h; cases h)
                hTy
            case «Type» =>
              exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
                (by intro T U h; cases h)
                (by intro T U h; cases h)
                hTy
            case Stuck =>
              exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
                (by intro T U h; cases h)
                (by intro T U h; cases h)
                hTy
            case FunType =>
              exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
                (by intro T U h; cases h)
                (by intro T U h; cases h)
                hTy
            case DatatypeType =>
              exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
                (by intro T U h; cases h)
                (by intro T U h; cases h)
                hTy
            case DatatypeTypeRef =>
              exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
                (by intro T U h; cases h)
                (by intro T U h; cases h)
                hTy
            case DtcAppType =>
              exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
                (by intro T U h; cases h)
                (by intro T U h; cases h)
                hTy
            case Var name T =>
              exact eo_type_valid_of_generic_apply_eq_dtcapp_full
                (f := Term.Var name T) (x := x) (A := a) (B := b)
                (go (Term.Var name T))
                (by
                  intro s d i j h
                  cases name <;>
                    first
                      | change SmtTerm.Var _ _ = SmtTerm.DtSel s d i j at h
                        cases h
                      | change SmtTerm.None = SmtTerm.DtSel s d i j at h
                        cases h)
                (by
                  intro s d i h
                  cases name <;>
                    first
                      | change SmtTerm.Var _ _ = SmtTerm.DtTester s d i at h
                        cases h
                      | change SmtTerm.None = SmtTerm.DtTester s d i at h
                        cases h)
                rfl rfl hTermNN hTy
            case DtCons s d i =>
              exact eo_type_valid_of_generic_apply_eq_dtcapp_full
                (f := Term.DtCons s d i) (x := x) (A := a) (B := b)
                (go (Term.DtCons s d i))
                (by
                  intro s' d' i' j' h
                  change
                    native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
                        (SmtTerm.DtCons s (__eo_to_smt_datatype_decl d) i) =
                      SmtTerm.DtSel s' d' i' j' at h
                  cases hRes : __eo_to_smt_reserved_datatype_name s <;>
                    simp [native_ite, hRes] at h)
                (by
                  intro s' d' i' h
                  change
                    native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
                        (SmtTerm.DtCons s (__eo_to_smt_datatype_decl d) i) =
                      SmtTerm.DtTester s' d' i' at h
                  cases hRes : __eo_to_smt_reserved_datatype_name s <;>
                    simp [native_ite, hRes] at h)
                rfl rfl hTermNN hTy
            case DtSel s d i j =>
              exact False.elim (false_of_eq_eo_dtcapp_type_of_no_smt_dtcapp_full
                (t := __eo_to_smt (Term.Apply (Term.DtSel s d i j) x))
                (a := a) (b := b)
                (by
                  rw [hEq]
                  change
                    __eo_to_smt_type
                      (__eo_typeof_apply
                        ((Term.FunType.Apply (Term.DatatypeType s d)).Apply
                          (__eo_typeof_dt_sel_return (__eo_dd_resolve s d) i j))
                        (__eo_typeof x)) =
                      __eo_to_smt_type (Term.DtcAppType a b)
                  rw [hTy])
                (by
                  intro hNone
                  apply hTypeNN
                  change
                    __eo_to_smt_type
                      (__eo_typeof_apply
                        ((Term.FunType.Apply (Term.DatatypeType s d)).Apply
                          (__eo_typeof_dt_sel_return (__eo_dd_resolve s d) i j))
                        (__eo_typeof x)) =
                      SmtType.None
                  rw [hTy]
                  exact hNone)
                (eo_to_smt_apply_dt_sel_ne_dtcapp_full s d i j x))
            case USort =>
              exact eo_type_valid_of_typeof_apply_eq_dtcapp_cases_full
                (by intro T U h; cases h)
                (by intro T U h; cases h)
                hTy
            case UConst i T =>
              exact eo_type_valid_of_generic_apply_eq_dtcapp_full
                (f := Term.UConst i T) (x := x) (A := a) (B := b)
                (go (Term.UConst i T))
                (by intro s d i j h; cases h)
                (by intro s d i h; cases h)
                rfl rfl hTermNN hTy
          all_goals
            rw [hTy] at hTypeNN
            simp [eo_type_valid, eo_type_valid_rec, __eo_to_smt_type, native_ite,
              native_Teq] at hTypeNN ⊢
      | Term.UOp1 UserOp1.seq_empty T, hNonNone => by
            change __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type T)) ≠
              SmtType.None at hNonNone
            refine ⟨?_, ?_⟩
            · change __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type T)) =
                __eo_to_smt_type (__eo_typeof (Term.seq_empty T))
              exact eo_to_smt_typeof_matches_translation_seq_empty T hNonNone
            · cases hTy : __eo_to_smt_type T <;> rw [hTy] at hNonNone <;>
                simp [__eo_to_smt_seq_empty] at hNonNone
              case Seq A =>
                have hSmt : __smtx_typeof (SmtTerm.seq_empty A) = SmtType.Seq A :=
                  smtx_typeof_seq_empty_of_non_none A hNonNone
                have hSeqWF : __smtx_type_wf (SmtType.Seq A) = true :=
                  Smtm.smtx_typeof_guard_wf_wf_of_non_none
                    (SmtType.Seq A) (SmtType.Seq A) (by
                      simpa [__smtx_typeof] using hNonNone)
                have hEq :=
                  eo_to_smt_typeof_matches_translation_seq_empty
                    T (by simpa [hTy, __eo_to_smt_seq_empty] using hNonNone)
                have hEoSeq :
                    __eo_to_smt_type (__eo_typeof (Term.seq_empty T)) =
                      SmtType.Seq A := by
                  rw [← hEq]
                  simpa [hTy, __eo_to_smt_seq_empty] using hSmt
                exact eo_type_valid_of_smt_wf (__eo_typeof (Term.seq_empty T))
                  (by simpa [hEoSeq] using hSeqWF)
      | Term.UOp1 UserOp1.set_empty T, hNonNone => by
            change __smtx_typeof (__eo_to_smt_set_empty (__eo_to_smt_type T)) ≠
              SmtType.None at hNonNone
            refine ⟨?_, ?_⟩
            · change __smtx_typeof (__eo_to_smt_set_empty (__eo_to_smt_type T)) =
                __eo_to_smt_type (__eo_typeof (Term.set_empty T))
              exact eo_to_smt_typeof_matches_translation_set_empty T hNonNone
            · cases hTy : __eo_to_smt_type T <;> rw [hTy] at hNonNone <;>
                simp [__eo_to_smt_set_empty] at hNonNone
              case Set A =>
                have hSmt : __smtx_typeof (SmtTerm.set_empty A) = SmtType.Set A :=
                  smtx_typeof_set_empty_of_non_none A hNonNone
                have hSetWF : __smtx_type_wf (SmtType.Set A) = true :=
                  Smtm.smtx_typeof_guard_wf_wf_of_non_none
                    (SmtType.Set A) (SmtType.Set A) (by
                      simpa [__smtx_typeof] using hNonNone)
                have hEq :=
                  eo_to_smt_typeof_matches_translation_set_empty
                    T (by simpa [hTy, __eo_to_smt_set_empty] using hNonNone)
                have hEoSet :
                    __eo_to_smt_type (__eo_typeof (Term.set_empty T)) =
                      SmtType.Set A := by
                  rw [← hEq]
                  simpa [hTy, __eo_to_smt_set_empty] using hSmt
                exact eo_type_valid_of_smt_wf (__eo_typeof (Term.set_empty T))
                  (by simpa [hEoSet] using hSetWF)
      | Term.UOp2 UserOp2._at_quantifiers_skolemize q idx, hNonNone => by
          cases q with
          | Apply qf body =>
              cases qf with
              | Apply qff xs =>
                  cases qff with
                  | UOp op =>
                      cases op
                      case «forall» =>
                        cases hIdxValid : __eo_to_smt_nat_is_valid idx
                        · exfalso
                          apply hNonNone
                          rw [show
                            __eo_to_smt
                                (Term.UOp2 UserOp2._at_quantifiers_skolemize
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body) idx) =
                              native_ite (__eo_to_smt_nat_is_valid idx)
                                (__eo_to_smt_quantifiers_skolemize
                                  xs (SmtTerm.not (__eo_to_smt body))
                                  (__eo_to_smt_nat idx))
                                SmtTerm.None by
                            rfl]
                          rw [hIdxValid]
                          simp [native_ite, smtx_typeof_none]
                        · refine ⟨?_, ?_⟩
                          · rw [show
                              __eo_to_smt
                                  (Term.UOp2 UserOp2._at_quantifiers_skolemize
                                    (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body) idx) =
                                native_ite (__eo_to_smt_nat_is_valid idx)
                                  (__eo_to_smt_quantifiers_skolemize
                                    xs (SmtTerm.not (__eo_to_smt body))
                                    (__eo_to_smt_nat idx))
                                  SmtTerm.None by
                              rfl]
                            rw [hIdxValid]
                            simp [native_ite]
                            have hSkolemNN :
                                __smtx_typeof
                                    (__eo_to_smt_quantifiers_skolemize
                                      xs (SmtTerm.not (__eo_to_smt body))
                                      (__eo_to_smt_nat idx)) ≠
                                  SmtType.None := by
                              have hNN := hNonNone
                              rw [show
                                __eo_to_smt
                                    (Term.UOp2 UserOp2._at_quantifiers_skolemize
                                      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body) idx) =
                                  native_ite (__eo_to_smt_nat_is_valid idx)
                                    (__eo_to_smt_quantifiers_skolemize
                                      xs (SmtTerm.not (__eo_to_smt body))
                                      (__eo_to_smt_nat idx))
                                    SmtTerm.None by
                                rfl] at hNN
                              rw [hIdxValid] at hNN
                              simpa [native_ite] using hNN
                            have hBodyNoExists :
                                ∀ s T F, SmtTerm.not (__eo_to_smt body) ≠ SmtTerm.exists s T F := by
                              intro s T F h
                              cases h
                            have hSkTy :=
                              eo_to_smt_quantifiers_skolemize_type_of_non_none xs
                                (SmtTerm.not (__eo_to_smt body)) (__eo_to_smt_nat idx)
                                hBodyNoExists hSkolemNN
                            cases idx with
                            | Numeral n =>
                                have hExistsBool :=
                                  eo_to_smt_exists_bool_of_quantifiers_skolemize_non_none xs
                                    (SmtTerm.not (__eo_to_smt body)) (native_int_to_nat n)
                                    hBodyNoExists hSkolemNN
                                have hXsList :
                                    __eo_typeof xs = Term.__eo_List :=
                                  eo_typeof_var_list_of_exists_bool xs
                                    (SmtTerm.not (__eo_to_smt body)) hExistsBool
                                have hNotBool :
                                    __smtx_typeof (SmtTerm.not (__eo_to_smt body)) = SmtType.Bool :=
                                  eo_to_smt_exists_body_bool_of_bool xs
                                    (SmtTerm.not (__eo_to_smt body)) hExistsBool
                                have hBodyBool :
                                    __smtx_typeof (__eo_to_smt body) = SmtType.Bool :=
                                  smtx_typeof_not_arg_bool (__eo_to_smt body) hNotBool
                                have hBodyNN :
                                    __smtx_typeof (__eo_to_smt body) ≠ SmtType.None := by
                                  rw [hBodyBool]
                                  simp
                                have hBodyBridge := go body hBodyNN
                                have hBodyEoSmt :
                                    __eo_to_smt_type (__eo_typeof body) = SmtType.Bool := by
                                  rw [← hBodyBridge.1, hBodyBool]
                                have hBodyEo : __eo_typeof body = Term.Bool :=
                                  eo_to_smt_type_eq_bool hBodyEoSmt
                                have hQType :
                                    __eo_typeof
                                        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body) =
                                      Term.Bool := by
                                  change __eo_typeof_forall (__eo_typeof xs) (__eo_typeof body) =
                                    Term.Bool
                                  rw [hXsList, hBodyEo]
                                  rfl
                                have hNat :
                                    native_nat_to_int (native_int_to_nat n) = n := by
                                  have hNonneg : 0 ≤ n := by
                                    exact of_decide_eq_true (by
                                      simpa [__eo_to_smt_nat_is_valid, native_zleq,
                                        SmtEval.native_zleq] using hIdxValid)
                                  simp [native_nat_to_int, native_int_to_nat,
                                    Smtm.native_nat_to_int, SmtEval.native_int_to_nat]
                                  exact Int.max_eq_left hNonneg
                                have hEoSk :
                                    __eo_to_smt_type
                                        (__eo_typeof
                                          (Term._at_quantifiers_skolemize
                                            (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body)
                                            (Term.Numeral n))) =
                                      __eo_to_smt_type
                                        (__get_var_type
                                          (__eo_list_nth Term.__eo_List_cons xs
                                            (Term.Numeral
                                              (native_nat_to_int (native_int_to_nat n))))) := by
                                  change
                                    __eo_to_smt_type
                                        (__eo_typeof__at_quantifiers_skolemize
                                          (__eo_typeof
                                            (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body))
                                          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body)
                                          (__eo_typeof (Term.Numeral n)) (Term.Numeral n)) =
                                      __eo_to_smt_type
                                        (__get_var_type
                                          (__eo_list_nth Term.__eo_List_cons xs
                                            (Term.Numeral
                                              (native_nat_to_int (native_int_to_nat n)))))
                                  rw [hQType]
                                  change
                                    __eo_to_smt_type
                                        (__get_nth_var_type
                                          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body)
                                          (Term.Numeral n)) =
                                      __eo_to_smt_type
                                        (__get_var_type
                                          (__eo_list_nth Term.__eo_List_cons xs
                                            (Term.Numeral
                                              (native_nat_to_int (native_int_to_nat n)))))
                                  change
                                    __eo_to_smt_type
                                        (__get_var_type
                                          (__eo_list_nth Term.__eo_List_cons xs (Term.Numeral n))) =
                                      __eo_to_smt_type
                                        (__get_var_type
                                          (__eo_list_nth Term.__eo_List_cons xs
                                            (Term.Numeral
                                              (native_nat_to_int (native_int_to_nat n)))))
                                  rw [hNat]
                                simpa [__eo_to_smt_nat] using hSkTy.trans hEoSk.symm
                            | _ =>
                                exfalso
                                simp [__eo_to_smt_nat_is_valid] at hIdxValid
                          · have hSkolemNN :
                                __smtx_typeof
                                    (__eo_to_smt_quantifiers_skolemize
                                      xs (SmtTerm.not (__eo_to_smt body))
                                      (__eo_to_smt_nat idx)) ≠
                                  SmtType.None := by
                              have hNN := hNonNone
                              rw [show
                                __eo_to_smt
                                    (Term.UOp2 UserOp2._at_quantifiers_skolemize
                                      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body) idx) =
                                  native_ite (__eo_to_smt_nat_is_valid idx)
                                    (__eo_to_smt_quantifiers_skolemize
                                      xs (SmtTerm.not (__eo_to_smt body))
                                      (__eo_to_smt_nat idx))
                                    SmtTerm.None by
                                rfl] at hNN
                              rw [hIdxValid] at hNN
                              simpa [native_ite] using hNN
                            have hBodyNoExists :
                                ∀ s T F, SmtTerm.not (__eo_to_smt body) ≠ SmtTerm.exists s T F := by
                              intro s T F h
                              cases h
                            cases idx with
                            | Numeral n =>
                                have hExistsBool :=
                                  eo_to_smt_exists_bool_of_quantifiers_skolemize_non_none xs
                                    (SmtTerm.not (__eo_to_smt body)) (native_int_to_nat n)
                                    hBodyNoExists hSkolemNN
                                have hXsList :
                                    __eo_typeof xs = Term.__eo_List :=
                                  eo_typeof_var_list_of_exists_bool xs
                                    (SmtTerm.not (__eo_to_smt body)) hExistsBool
                                have hNotBool :
                                    __smtx_typeof (SmtTerm.not (__eo_to_smt body)) = SmtType.Bool :=
                                  eo_to_smt_exists_body_bool_of_bool xs
                                    (SmtTerm.not (__eo_to_smt body)) hExistsBool
                                have hBodyBool :
                                    __smtx_typeof (__eo_to_smt body) = SmtType.Bool :=
                                  smtx_typeof_not_arg_bool (__eo_to_smt body) hNotBool
                                have hBodyNN :
                                    __smtx_typeof (__eo_to_smt body) ≠ SmtType.None := by
                                  rw [hBodyBool]
                                  simp
                                have hBodyBridge := go body hBodyNN
                                have hBodyEoSmt :
                                    __eo_to_smt_type (__eo_typeof body) = SmtType.Bool := by
                                  rw [← hBodyBridge.1, hBodyBool]
                                have hBodyEo : __eo_typeof body = Term.Bool :=
                                  eo_to_smt_type_eq_bool hBodyEoSmt
                                have hQType :
                                    __eo_typeof
                                        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body) =
                                      Term.Bool := by
                                  change __eo_typeof_forall (__eo_typeof xs) (__eo_typeof body) =
                                    Term.Bool
                                  rw [hXsList, hBodyEo]
                                  rfl
                                have hNat :
                                    native_nat_to_int (native_int_to_nat n) = n := by
                                  have hNonneg : 0 ≤ n := by
                                    exact of_decide_eq_true (by
                                      simpa [__eo_to_smt_nat_is_valid, native_zleq,
                                        SmtEval.native_zleq] using hIdxValid)
                                  simp [native_nat_to_int, native_int_to_nat,
                                    Smtm.native_nat_to_int, SmtEval.native_int_to_nat]
                                  exact Int.max_eq_left hNonneg
                                have hSkValid :=
                                  eo_to_smt_quantifiers_skolemize_var_type_valid_of_non_none xs
                                    (SmtTerm.not (__eo_to_smt body)) (native_int_to_nat n)
                                    hBodyNoExists hSkolemNN
                                change
                                  eo_type_valid
                                    (__eo_typeof__at_quantifiers_skolemize
                                      (__eo_typeof
                                        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body))
                                      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body)
                                      (__eo_typeof (Term.Numeral n)) (Term.Numeral n))
                                rw [hQType]
                                change
                                  eo_type_valid
                                    (__get_var_type
                                      (__eo_list_nth Term.__eo_List_cons xs (Term.Numeral n)))
                                simpa [hNat] using hSkValid
                            | _ =>
                                exfalso
                                simp [__eo_to_smt_nat_is_valid] at hIdxValid
                      all_goals
                        exact false_of_smtx_typeof_none_non_none_full hNonNone
                  | _ =>
                      exact false_of_smtx_typeof_none_non_none_full hNonNone
              | _ =>
                  exact false_of_smtx_typeof_none_non_none_full hNonNone
          | _ =>
              exact false_of_smtx_typeof_none_non_none_full hNonNone
    | Term.__eo_List, hNonNone => by
        exact false_of_smtx_typeof_none_non_none_full hNonNone
    | Term.__eo_List_nil, hNonNone => by
        exact false_of_smtx_typeof_none_non_none_full hNonNone
    | Term.__eo_List_cons, hNonNone => by
        exact false_of_smtx_typeof_none_non_none_full hNonNone
    | Term.Bool, hNonNone => by
        exact false_of_smtx_typeof_none_non_none_full hNonNone
    | Term.Type, hNonNone => by
        exact false_of_smtx_typeof_none_non_none_full hNonNone
    | Term.Stuck, hNonNone => by
        exact false_of_smtx_typeof_none_non_none_full hNonNone
    | Term.FunType, hNonNone => by
          exact false_of_smtx_typeof_none_non_none_full hNonNone
      | Term.DatatypeType s d, hNonNone => by
          exact false_of_smtx_typeof_none_non_none_full hNonNone
      | Term.DatatypeTypeRef s, hNonNone => by
          exact false_of_smtx_typeof_none_non_none_full hNonNone
      | Term.DtcAppType T U, hNonNone => by
          exact false_of_smtx_typeof_none_non_none_full hNonNone
    | Term.DtSel s d i j, hNonNone => by
        exfalso
        apply hNonNone
        cases hRes : __eo_reserved_datatype_name s <;>
          rw [eo_to_smt_term_dt_sel, hRes] <;>
          simp [native_ite, smtx_typeof_none, smtx_typeof_dt_sel_head_none]
    | Term.USort i, hNonNone => by
        exact false_of_smtx_typeof_none_non_none_full hNonNone
    | Term.UOp3 UserOp3._at_re_unfold_pos_component str re idx, hNonNone => by
        exact
          eo_to_smt_typeof_matches_translation_apply_apply_apply_re_unfold_pos_component
            idx re str
            (fun h => (go str h).1)
            (fun h => (go re h).1)
            hNonNone
    | Term.UOp3 UserOp3._at_witness_string_length T len id, hNonNone => by
        have hEq :=
          eo_to_smt_typeof_matches_translation_apply_apply_apply_at_witness_string_length
            id len T (fun h => (go len h).1) (fun h => (go id h).1) hNonNone
        refine ⟨hEq, ?_⟩
        let ST := __eo_to_smt_type T
        let body :=
          SmtTerm.eq
            (SmtTerm.str_len (SmtTerm.Var (native_string_lit "@x") ST))
            (__eo_to_smt len)
        have hTranslate :
            __eo_to_smt (Term.UOp3 UserOp3._at_witness_string_length T len id) =
              native_ite (__eo_to_smt_nat_is_valid len)
                (native_ite (__eo_to_smt_nat_is_valid id)
                  (SmtTerm.choice (native_string_lit "@x") ST body)
                  SmtTerm.None)
                SmtTerm.None := by
          rfl
        have hLenValid : __eo_to_smt_nat_is_valid len = true := by
          cases hTest : __eo_to_smt_nat_is_valid len
          · exfalso
            apply hNonNone
            rw [hTranslate]
            simp [hTest, native_ite]
          · rfl
        have hIdValid : __eo_to_smt_nat_is_valid id = true := by
          cases hTest : __eo_to_smt_nat_is_valid id
          · exfalso
            apply hNonNone
            rw [hTranslate]
            simp [hLenValid, hTest, native_ite]
          · rfl
        have hIdInt : __eo_typeof id = Term.UOp UserOp.Int :=
          eo_typeof_eq_int_of_nat_is_valid id hIdValid
        have hLenInt : __eo_typeof len = Term.UOp UserOp.Int :=
          eo_typeof_eq_int_of_nat_is_valid len hLenValid
        have hChoiceNN :
            term_has_non_none_type (SmtTerm.choice (native_string_lit "@x") ST body) := by
          unfold term_has_non_none_type
          have hTermNN' := hNonNone
          rw [hTranslate] at hTermNN'
          simpa [hLenValid, hIdValid, native_ite] using hTermNN'
        have hChoiceGuard :
            __smtx_typeof (SmtTerm.choice (native_string_lit "@x") ST body) =
              __smtx_typeof_guard_wf ST ST :=
          choice_term_guard_type_of_non_none hChoiceNN
        have hGuardNN : __smtx_typeof_guard_wf ST ST ≠ SmtType.None := by
          intro hNone
          unfold term_has_non_none_type at hChoiceNN
          exact hChoiceNN (by rw [hChoiceGuard, hNone])
        have hTWF : __smtx_type_wf ST = true :=
          Smtm.smtx_typeof_guard_wf_wf_of_non_none ST ST hGuardNN
        have hTType : __eo_typeof T = Term.Type :=
          eo_typeof_type_of_smt_type_wf T (by simpa [ST] using hTWF)
        have hTValid : eo_type_valid T :=
          eo_type_valid_of_smt_wf T (by simpa [ST] using hTWF)
        have hTNonStuck : T ≠ Term.Stuck := by
          intro h
          subst T
          cases hTType
        have hTypeEq :
            __eo_typeof (Term.UOp3 UserOp3._at_witness_string_length T len id) = T := by
          change
            __eo_typeof__at_witness_string_length
              (__eo_typeof T) T (__eo_typeof len) (__eo_typeof id) = T
          rw [hTType, hLenInt, hIdInt]
          exact eo_typeof_at_witness_string_length_of_non_stuck_full T hTNonStuck
        rw [hTypeEq]
        exact hTValid
    | Term.UOp2 UserOp2._at_const v T, hNonNone => by
        cases hValid : __eo_to_smt_nat_is_valid v
        case false =>
          exact False.elim (hNonNone (by
            rw [eo_to_smt_at_const_of_invalid hValid]
            exact smtx_typeof_none))
        case true =>
          rw [eo_to_smt_at_const_of_valid hValid] at hNonNone ⊢
          have hTWF : __smtx_type_wf (__eo_to_smt_type T) = true :=
            Smtm.smtx_typeof_guard_wf_wf_of_non_none
              (__eo_to_smt_type T) (__eo_to_smt_type T) (by
                simpa [__smtx_typeof] using hNonNone)
          have hTType : __eo_typeof T = Term.Type :=
            eo_typeof_type_of_smt_type_wf T hTWF
          have hTypeEq : __eo_typeof (Term.UOp2 UserOp2._at_const v T) = T :=
            eo_typeof_at_const hValid hTType
          rw [hTypeEq]
          exact ⟨smtx_typeof_uconst_of_non_none _ (__eo_to_smt_type T) hNonNone,
            eo_type_valid_of_smt_wf T hTWF⟩
  exact go t

/-- Direct form of the translation typing theorem. -/
theorem eo_to_smt_typeof_matches_translation
    (t : Term) :
    __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t) := by
  intro hNonNone
  exact (eo_to_smt_typeof_matches_translation_and_valid t hNonNone).1

theorem eo_type_valid_typeof_of_smt_translation
    (t : Term) :
    __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
    eo_type_valid (__eo_typeof t) := by
  intro hNonNone
  exact (eo_to_smt_typeof_matches_translation_and_valid t hNonNone).2

theorem eo_to_smt_typed_list_elem_type_of_non_none
    (xs : Term) :
    __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ->
      ∃ T,
        __eo_typeof xs = Term.Apply (Term.UOp UserOp._at__at_TypedList) T ∧
          __eo_to_smt_type T = __eo_to_smt_typed_list_elem_type xs ∧
          eo_type_valid T := by
  intro hNonNone
  exact eo_to_smt_typed_list_elem_type_of_non_none_full
    (Term.Apply (Term.UOp UserOp.distinct) xs)
    (fun term _ hNN => eo_to_smt_typeof_matches_translation_and_valid term hNN)
    xs (by simp) hNonNone

/--
Post-induction form of EO type recovery from SMT typing.

This is the proof term we want for the deferred recovery theorem once the
remaining early callers are rewritten to use explicit induction hypotheses
instead of importing the full translation theorem.
-/
theorem eo_to_smt_type_typeof_of_smt_type_from_full
    (t : Term) {T : SmtType}
    (h : __smtx_typeof (__eo_to_smt t) = T)
    (hT : T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof t) = T := by
  have hNonNone : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None := by
    rw [h]
    exact hT
  exact (eo_to_smt_typeof_matches_translation t hNonNone).symm.trans h

end TranslationProofs
