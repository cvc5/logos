module

public import Cpc.Proofs.RuleSupport.CnfSupport
import all Cpc.Proofs.RuleSupport.CnfSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private abbrev eoAnd (A B : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B

private abbrev eoOr (A B : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B

private abbrev mkOr (A B : Term) : Term :=
  __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.or) A) B

private abbrev tailAnd (y ys : Term) : Term :=
  eoAnd y ys

private abbrev singletonAnd (y ys : Term) : Term :=
  __eo_list_singleton_elim (Term.UOp UserOp.and) (tailAnd y ys)

private abbrev tailOr (z zs : Term) : Term :=
  eoOr z zs

private abbrev lhsOrAndDistrib (y1 y2 ys z zs : Term) : Term :=
  eoOr (eoAnd y1 (tailAnd y2 ys)) (tailOr z zs)

private abbrev rhsOrAndDistrib (y1 y2 ys z zs : Term) : Term :=
  __eo_mk_apply (Term.Apply (Term.UOp UserOp.and) (eoOr y1 (tailOr z zs)))
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.and) (mkOr (singletonAnd y2 ys) (tailOr z zs)))
      (Term.Boolean true))

private theorem prog_bool_or_and_distrib_eq_of_ne_stuck (y1 y2 ys z zs : Term) :
    y1 ≠ Term.Stuck ->
    y2 ≠ Term.Stuck ->
    ys ≠ Term.Stuck ->
    z ≠ Term.Stuck ->
    zs ≠ Term.Stuck ->
    __eo_prog_bool_or_and_distrib y1 y2 ys z zs =
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq)
        (lhsOrAndDistrib y1 y2 ys z zs))
        (rhsOrAndDistrib y1 y2 ys z zs) := by
  intro hY1 hY2 hYs hZ hZs
  simp [__eo_prog_bool_or_and_distrib, lhsOrAndDistrib, rhsOrAndDistrib,
    singletonAnd, tailAnd, tailOr, mkOr, eoAnd, eoOr]

private theorem typeof_eq_or_left_bool {A B C : Term} :
    __eo_typeof_eq (__eo_typeof (eoOr A B)) (__eo_typeof C) = Term.Bool ->
    __eo_typeof A = Term.Bool ∧ __eo_typeof B = Term.Bool ∧
      __eo_typeof C = Term.Bool := by
  intro hTy
  change __eo_typeof_eq (__eo_typeof_or (__eo_typeof A) (__eo_typeof B))
    (__eo_typeof C) = Term.Bool at hTy
  cases hA : __eo_typeof A <;> cases hB : __eo_typeof B <;>
    cases hC : __eo_typeof C <;>
    simp [__eo_typeof_eq, __eo_typeof_or, __eo_requires, __eo_eq,
      native_ite, native_teq, native_not, hA, hB, hC] at hTy ⊢

private theorem typeof_mk_or_left_bool {A B : Term} :
    __eo_typeof (mkOr A B) = Term.Bool ->
    __eo_typeof A = Term.Bool := by
  intro hTy
  change __eo_typeof (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.or) A) B) =
    Term.Bool at hTy
  have hOuterNe :
      __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.or) A) B ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  have hFnNe : __eo_mk_apply (Term.UOp UserOp.or) A ≠ Term.Stuck :=
    CnfSupport.mk_apply_ne_stuck_left hOuterNe
  have hANe : A ≠ Term.Stuck :=
    CnfSupport.mk_apply_ne_stuck_right hFnNe
  have hFnEq :
      __eo_mk_apply (Term.UOp UserOp.or) A =
        Term.Apply (Term.UOp UserOp.or) A :=
    CnfSupport.mk_apply_eq_apply (f := Term.UOp UserOp.or) (a := A)
      (by simp) hANe
  have hOuterNe' :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.or) A) B ≠ Term.Stuck := by
    simpa [hFnEq] using hOuterNe
  have hBNe : B ≠ Term.Stuck :=
    CnfSupport.mk_apply_ne_stuck_right hOuterNe'
  have hTy' := hTy
  rw [hFnEq] at hTy'
  rw [CnfSupport.mk_apply_eq_apply
    (f := Term.Apply (Term.UOp UserOp.or) A) (a := B)
    (by simp) hBNe] at hTy'
  change __eo_typeof_or (__eo_typeof A) (__eo_typeof B) = Term.Bool at hTy'
  exact CnfSupport.typeof_or_eq_bool_left hTy'

private theorem eo_has_bool_type_mk_and
    (A B : Term) :
    RuleProofs.eo_has_bool_type A ->
    RuleProofs.eo_has_bool_type B ->
    RuleProofs.eo_has_bool_type (__eo_mk_apply (Term.Apply (Term.UOp UserOp.and) A) B) := by
  intro hA hB
  have hBNe : B ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type B hB
  rw [CnfSupport.mk_apply_eq_apply (f := Term.Apply (Term.UOp UserOp.and) A)
    (a := B) (by simp) hBNe]
  exact RuleProofs.eo_has_bool_type_and_of_bool_args A B hA hB

private theorem eo_has_bool_type_mk_and_chain
    (A B : Term) :
    RuleProofs.eo_has_bool_type A ->
    RuleProofs.eo_has_bool_type B ->
    RuleProofs.eo_has_bool_type (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.and) A) B) := by
  intro hA hB
  have hANe : A ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type A hA
  rw [CnfSupport.mk_apply_eq_apply (f := Term.UOp UserOp.and) (a := A)
    (by simp) hANe]
  exact eo_has_bool_type_mk_and A B hA hB

private theorem eo_has_bool_type_mk_or
    (A B : Term) :
    RuleProofs.eo_has_bool_type A ->
    RuleProofs.eo_has_bool_type B ->
    RuleProofs.eo_has_bool_type (__eo_mk_apply (Term.Apply (Term.UOp UserOp.or) A) B) := by
  intro hA hB
  have hBNe : B ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type B hB
  rw [CnfSupport.mk_apply_eq_apply (f := Term.Apply (Term.UOp UserOp.or) A)
    (a := B) (by simp) hBNe]
  exact RuleProofs.eo_has_bool_type_or_of_bool_args A B hA hB

private theorem eo_has_bool_type_mk_or_chain
    (A B : Term) :
    RuleProofs.eo_has_bool_type A ->
    RuleProofs.eo_has_bool_type B ->
    RuleProofs.eo_has_bool_type (mkOr A B) := by
  intro hA hB
  have hANe : A ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type A hA
  change RuleProofs.eo_has_bool_type
    (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.or) A) B)
  rw [CnfSupport.mk_apply_eq_apply (f := Term.UOp UserOp.or) (a := A)
    (by simp) hANe]
  exact eo_has_bool_type_mk_or A B hA hB

private theorem bool_or_and_distrib_data (y1 y2 ys z zs : Term) :
    RuleProofs.eo_has_smt_translation y1 ->
    RuleProofs.eo_has_smt_translation y2 ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation zs ->
    __eo_typeof (__eo_prog_bool_or_and_distrib y1 y2 ys z zs) = Term.Bool ->
    RuleProofs.eo_has_bool_type y1 ∧
      RuleProofs.eo_has_bool_type y2 ∧
      RuleProofs.eo_has_bool_type ys ∧
      RuleProofs.eo_has_bool_type z ∧
      RuleProofs.eo_has_bool_type zs ∧
      CnfSupport.AndList (tailAnd y2 ys) ∧
      RuleProofs.eo_has_bool_type (singletonAnd y2 ys) := by
  intro hY1Trans hY2Trans hYsTrans hZTrans hZsTrans hResultTy
  have hY1Ne : y1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y1 hY1Trans
  have hY2Ne : y2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y2 hY2Trans
  have hYsNe : ys ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation ys hYsTrans
  have hZNe : z ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation z hZTrans
  have hZsNe : zs ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation zs hZsTrans
  have hProgEq :=
    prog_bool_or_and_distrib_eq_of_ne_stuck y1 y2 ys z zs
      hY1Ne hY2Ne hYsNe hZNe hZsNe
  have hProgNe : __eo_prog_bool_or_and_distrib y1 y2 ys z zs ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  rw [hProgEq] at hProgNe hResultTy
  have hRhsNe : rhsOrAndDistrib y1 y2 ys z zs ≠ Term.Stuck :=
    CnfSupport.mk_apply_ne_stuck_right hProgNe
  have hResultTy' :
      __eo_typeof
        (__eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq) (lhsOrAndDistrib y1 y2 ys z zs))
          (rhsOrAndDistrib y1 y2 ys z zs)) = Term.Bool := hResultTy
  rw [CnfSupport.mk_apply_eq_apply
    (f := Term.Apply (Term.UOp UserOp.eq) (lhsOrAndDistrib y1 y2 ys z zs))
    (a := rhsOrAndDistrib y1 y2 ys z zs) (by simp) hRhsNe] at hResultTy'
  change __eo_typeof_eq (__eo_typeof (lhsOrAndDistrib y1 y2 ys z zs))
    (__eo_typeof (rhsOrAndDistrib y1 y2 ys z zs)) = Term.Bool at hResultTy'
  rcases typeof_eq_or_left_bool (A := eoAnd y1 (tailAnd y2 ys)) (B := tailOr z zs)
      (C := rhsOrAndDistrib y1 y2 ys z zs) hResultTy' with
    ⟨hLeftAndType, hTailOrType, hRhsType⟩
  change __eo_typeof_or (__eo_typeof y1) (__eo_typeof (tailAnd y2 ys)) =
    Term.Bool at hLeftAndType
  have hY1Type : __eo_typeof y1 = Term.Bool :=
    CnfSupport.typeof_or_eq_bool_left hLeftAndType
  have hTailAndType : __eo_typeof (tailAnd y2 ys) = Term.Bool :=
    CnfSupport.typeof_or_eq_bool_right hLeftAndType
  change __eo_typeof_or (__eo_typeof y2) (__eo_typeof ys) = Term.Bool at hTailAndType
  have hY2Type : __eo_typeof y2 = Term.Bool :=
    CnfSupport.typeof_or_eq_bool_left hTailAndType
  have hYsType : __eo_typeof ys = Term.Bool :=
    CnfSupport.typeof_or_eq_bool_right hTailAndType
  change __eo_typeof_or (__eo_typeof z) (__eo_typeof zs) = Term.Bool at hTailOrType
  have hZType : __eo_typeof z = Term.Bool :=
    CnfSupport.typeof_or_eq_bool_left hTailOrType
  have hZsType : __eo_typeof zs = Term.Bool :=
    CnfSupport.typeof_or_eq_bool_right hTailOrType
  have hInnerType :
      __eo_typeof
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.and)
            (mkOr (singletonAnd y2 ys) (tailOr z zs)))
          (Term.Boolean true)) = Term.Bool :=
    CnfSupport.typeof_mk_apply_and_right_bool hRhsType
  have hInnerNe :
      __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.and)
          (mkOr (singletonAnd y2 ys) (tailOr z zs)))
        (Term.Boolean true) ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hInnerType
  have hInnerFnNe :
      __eo_mk_apply (Term.UOp UserOp.and)
        (mkOr (singletonAnd y2 ys) (tailOr z zs)) ≠ Term.Stuck :=
    CnfSupport.mk_apply_ne_stuck_left hInnerNe
  have hMkOrNe : mkOr (singletonAnd y2 ys) (tailOr z zs) ≠ Term.Stuck :=
    CnfSupport.mk_apply_ne_stuck_right hInnerFnNe
  have hInnerType' := hInnerType
  rw [CnfSupport.mk_apply_eq_apply (f := Term.UOp UserOp.and)
    (a := mkOr (singletonAnd y2 ys) (tailOr z zs)) (by simp) hMkOrNe]
    at hInnerType'
  have hMkOrType :
      __eo_typeof (mkOr (singletonAnd y2 ys) (tailOr z zs)) = Term.Bool :=
    CnfSupport.typeof_mk_apply_and_left_bool hInnerType'
  have hSingletonType : __eo_typeof (singletonAnd y2 ys) = Term.Bool :=
    typeof_mk_or_left_bool hMkOrType
  have hSingletonNe : singletonAnd y2 ys ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hSingletonType
  have hTailList : CnfSupport.AndList (tailAnd y2 ys) :=
    CnfSupport.andList_of_singleton_elim_ne_stuck hSingletonNe
  have hY1Bool : RuleProofs.eo_has_bool_type y1 :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      y1 Term.Bool (__eo_to_smt y1) rfl hY1Trans hY1Type
  have hY2Bool : RuleProofs.eo_has_bool_type y2 :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      y2 Term.Bool (__eo_to_smt y2) rfl hY2Trans hY2Type
  have hYsBool : RuleProofs.eo_has_bool_type ys :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      ys Term.Bool (__eo_to_smt ys) rfl hYsTrans hYsType
  have hZBool : RuleProofs.eo_has_bool_type z :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      z Term.Bool (__eo_to_smt z) rfl hZTrans hZType
  have hZsBool : RuleProofs.eo_has_bool_type zs :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      zs Term.Bool (__eo_to_smt zs) rfl hZsTrans hZsType
  have hTailAndBool : RuleProofs.eo_has_bool_type (tailAnd y2 ys) :=
    RuleProofs.eo_has_bool_type_and_of_bool_args y2 ys hY2Bool hYsBool
  have hSingletonBool : RuleProofs.eo_has_bool_type (singletonAnd y2 ys) :=
    CnfSupport.andList_singleton_elim_preserves_bool_type hTailList hTailAndBool
  exact ⟨hY1Bool, hY2Bool, hYsBool, hZBool, hZsBool, hTailList, hSingletonBool⟩

private theorem typed___eo_prog_bool_or_and_distrib_impl (y1 y2 ys z zs : Term) :
    RuleProofs.eo_has_smt_translation y1 ->
    RuleProofs.eo_has_smt_translation y2 ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation zs ->
    __eo_typeof (__eo_prog_bool_or_and_distrib y1 y2 ys z zs) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__eo_prog_bool_or_and_distrib y1 y2 ys z zs) := by
  intro hY1Trans hY2Trans hYsTrans hZTrans hZsTrans hResultTy
  have hY1Ne : y1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y1 hY1Trans
  have hY2Ne : y2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y2 hY2Trans
  have hYsNe : ys ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation ys hYsTrans
  have hZNe : z ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation z hZTrans
  have hZsNe : zs ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation zs hZsTrans
  rcases bool_or_and_distrib_data y1 y2 ys z zs hY1Trans hY2Trans hYsTrans
      hZTrans hZsTrans hResultTy with
    ⟨hY1Bool, hY2Bool, hYsBool, hZBool, hZsBool, hTailList, hSingletonBool⟩
  have hTailAndBool : RuleProofs.eo_has_bool_type (tailAnd y2 ys) :=
    RuleProofs.eo_has_bool_type_and_of_bool_args y2 ys hY2Bool hYsBool
  have hTailOrBool : RuleProofs.eo_has_bool_type (tailOr z zs) :=
    RuleProofs.eo_has_bool_type_or_of_bool_args z zs hZBool hZsBool
  have hAndBool : RuleProofs.eo_has_bool_type (eoAnd y1 (tailAnd y2 ys)) :=
    RuleProofs.eo_has_bool_type_and_of_bool_args y1 (tailAnd y2 ys)
      hY1Bool hTailAndBool
  have hLeftBool : RuleProofs.eo_has_bool_type (lhsOrAndDistrib y1 y2 ys z zs) :=
    RuleProofs.eo_has_bool_type_or_of_bool_args (eoAnd y1 (tailAnd y2 ys))
      (tailOr z zs) hAndBool hTailOrBool
  have hY1OrBool : RuleProofs.eo_has_bool_type (eoOr y1 (tailOr z zs)) :=
    RuleProofs.eo_has_bool_type_or_of_bool_args y1 (tailOr z zs)
      hY1Bool hTailOrBool
  have hSingletonOrBool :
      RuleProofs.eo_has_bool_type (mkOr (singletonAnd y2 ys) (tailOr z zs)) :=
    eo_has_bool_type_mk_or_chain (singletonAnd y2 ys) (tailOr z zs)
      hSingletonBool hTailOrBool
  have hInnerBool :
      RuleProofs.eo_has_bool_type
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.and)
            (mkOr (singletonAnd y2 ys) (tailOr z zs)))
          (Term.Boolean true)) :=
    eo_has_bool_type_mk_and_chain (mkOr (singletonAnd y2 ys) (tailOr z zs))
      (Term.Boolean true) hSingletonOrBool RuleProofs.eo_has_bool_type_true
  have hRhsBool : RuleProofs.eo_has_bool_type (rhsOrAndDistrib y1 y2 ys z zs) :=
    eo_has_bool_type_mk_and (eoOr y1 (tailOr z zs))
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.and)
          (mkOr (singletonAnd y2 ys) (tailOr z zs)))
        (Term.Boolean true))
      hY1OrBool hInnerBool
  have hProgEq :=
    prog_bool_or_and_distrib_eq_of_ne_stuck y1 y2 ys z zs
      hY1Ne hY2Ne hYsNe hZNe hZsNe
  rw [hProgEq]
  have hRhsNe : rhsOrAndDistrib y1 y2 ys z zs ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type _ hRhsBool
  rw [CnfSupport.mk_apply_eq_apply
    (f := Term.Apply (Term.UOp UserOp.eq) (lhsOrAndDistrib y1 y2 ys z zs))
    (a := rhsOrAndDistrib y1 y2 ys z zs) (by simp) hRhsNe]
  exact CnfSupport.eo_has_bool_type_eq_of_bool_args
    (lhsOrAndDistrib y1 y2 ys z zs) (rhsOrAndDistrib y1 y2 ys z zs)
    hLeftBool hRhsBool

private theorem bool_eval_eq_of_true_iff
    (M : SmtModel) (hM : model_wf M) (A B : Term) :
    RuleProofs.eo_has_bool_type A ->
    RuleProofs.eo_has_bool_type B ->
    (eo_interprets M A true ↔ eo_interprets M B true) ->
    __smtx_model_eval M (__eo_to_smt A) =
      __smtx_model_eval M (__eo_to_smt B) := by
  intro hABool hBBool hIff
  rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM A hABool with
    ⟨a, hEvalA⟩
  rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM B hBBool with
    ⟨b, hEvalB⟩
  cases a <;> cases b
  · rw [hEvalA, hEvalB]
  · have hBTrue : eo_interprets M B true :=
      RuleProofs.eo_interprets_of_bool_eval M B true hBBool hEvalB
    have hATrue : eo_interprets M A true := hIff.mpr hBTrue
    have hAFalse : eo_interprets M A false :=
      RuleProofs.eo_interprets_of_bool_eval M A false hABool hEvalA
    exact False.elim ((RuleProofs.eo_interprets_true_not_false M A hATrue) hAFalse)
  · have hATrue : eo_interprets M A true :=
      RuleProofs.eo_interprets_of_bool_eval M A true hABool hEvalA
    have hBTrue : eo_interprets M B true := hIff.mp hATrue
    have hBFalse : eo_interprets M B false :=
      RuleProofs.eo_interprets_of_bool_eval M B false hBBool hEvalB
    exact False.elim ((RuleProofs.eo_interprets_true_not_false M B hBTrue) hBFalse)
  · rw [hEvalA, hEvalB]

private theorem facts___eo_prog_bool_or_and_distrib_impl
    (M : SmtModel) (hM : model_wf M) (y1 y2 ys z zs : Term) :
    RuleProofs.eo_has_smt_translation y1 ->
    RuleProofs.eo_has_smt_translation y2 ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation zs ->
    __eo_typeof (__eo_prog_bool_or_and_distrib y1 y2 ys z zs) = Term.Bool ->
    eo_interprets M (__eo_prog_bool_or_and_distrib y1 y2 ys z zs) true := by
  intro hY1Trans hY2Trans hYsTrans hZTrans hZsTrans hResultTy
  have hY1Ne : y1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y1 hY1Trans
  have hY2Ne : y2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y2 hY2Trans
  have hYsNe : ys ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation ys hYsTrans
  have hZNe : z ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation z hZTrans
  have hZsNe : zs ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation zs hZsTrans
  rcases bool_or_and_distrib_data y1 y2 ys z zs hY1Trans hY2Trans hYsTrans
      hZTrans hZsTrans hResultTy with
    ⟨hY1Bool, hY2Bool, hYsBool, hZBool, hZsBool, hTailList, hSingletonBool⟩
  have hTailAndBool : RuleProofs.eo_has_bool_type (tailAnd y2 ys) :=
    RuleProofs.eo_has_bool_type_and_of_bool_args y2 ys hY2Bool hYsBool
  have hTailOrBool : RuleProofs.eo_has_bool_type (tailOr z zs) :=
    RuleProofs.eo_has_bool_type_or_of_bool_args z zs hZBool hZsBool
  have hAndBool : RuleProofs.eo_has_bool_type (eoAnd y1 (tailAnd y2 ys)) :=
    RuleProofs.eo_has_bool_type_and_of_bool_args y1 (tailAnd y2 ys)
      hY1Bool hTailAndBool
  have hLeftBool : RuleProofs.eo_has_bool_type (lhsOrAndDistrib y1 y2 ys z zs) :=
    RuleProofs.eo_has_bool_type_or_of_bool_args (eoAnd y1 (tailAnd y2 ys))
      (tailOr z zs) hAndBool hTailOrBool
  have hProgBool :
      RuleProofs.eo_has_bool_type (__eo_prog_bool_or_and_distrib y1 y2 ys z zs) :=
    typed___eo_prog_bool_or_and_distrib_impl y1 y2 ys z zs
      hY1Trans hY2Trans hYsTrans hZTrans hZsTrans hResultTy
  have hProgEq :=
    prog_bool_or_and_distrib_eq_of_ne_stuck y1 y2 ys z zs
      hY1Ne hY2Ne hYsNe hZNe hZsNe
  rw [hProgEq]
  have hY1OrBool : RuleProofs.eo_has_bool_type (eoOr y1 (tailOr z zs)) :=
    RuleProofs.eo_has_bool_type_or_of_bool_args y1 (tailOr z zs)
      hY1Bool hTailOrBool
  have hSingletonOrBool :
      RuleProofs.eo_has_bool_type (mkOr (singletonAnd y2 ys) (tailOr z zs)) :=
    eo_has_bool_type_mk_or_chain (singletonAnd y2 ys) (tailOr z zs)
      hSingletonBool hTailOrBool
  have hInnerBool :
      RuleProofs.eo_has_bool_type
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.and)
            (mkOr (singletonAnd y2 ys) (tailOr z zs)))
          (Term.Boolean true)) :=
    eo_has_bool_type_mk_and_chain (mkOr (singletonAnd y2 ys) (tailOr z zs))
      (Term.Boolean true) hSingletonOrBool RuleProofs.eo_has_bool_type_true
  have hRhsBool : RuleProofs.eo_has_bool_type (rhsOrAndDistrib y1 y2 ys z zs) :=
    eo_has_bool_type_mk_and (eoOr y1 (tailOr z zs))
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.and)
          (mkOr (singletonAnd y2 ys) (tailOr z zs)))
        (Term.Boolean true))
      hY1OrBool hInnerBool
  have hRhsNe : rhsOrAndDistrib y1 y2 ys z zs ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type _ hRhsBool
  rw [CnfSupport.mk_apply_eq_apply
    (f := Term.Apply (Term.UOp UserOp.eq) (lhsOrAndDistrib y1 y2 ys z zs))
    (a := rhsOrAndDistrib y1 y2 ys z zs) (by simp) hRhsNe]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [hProgEq, CnfSupport.mk_apply_eq_apply
      (f := Term.Apply (Term.UOp UserOp.eq) (lhsOrAndDistrib y1 y2 ys z zs))
      (a := rhsOrAndDistrib y1 y2 ys z zs) (by simp) hRhsNe] using hProgBool
  · rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM y1 hY1Bool with
      ⟨by1, hEvalY1⟩
    rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM
        (tailAnd y2 ys) hTailAndBool with
      ⟨bt, hEvalTailAnd⟩
    rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM
        (tailOr z zs) hTailOrBool with
      ⟨bz, hEvalTailOr⟩
    have hSingletonEval :
        __smtx_model_eval M (__eo_to_smt (singletonAnd y2 ys)) =
          __smtx_model_eval M (__eo_to_smt (tailAnd y2 ys)) :=
      bool_eval_eq_of_true_iff M hM (singletonAnd y2 ys) (tailAnd y2 ys)
        hSingletonBool hTailAndBool
        (CnfSupport.andList_singleton_elim_true_iff M hTailList hTailAndBool)
    have hSingletonNe : singletonAnd y2 ys ≠ Term.Stuck :=
      RuleProofs.term_ne_stuck_of_has_bool_type _ hSingletonBool
    have hTailOrNe : tailOr z zs ≠ Term.Stuck :=
      RuleProofs.term_ne_stuck_of_has_bool_type _ hTailOrBool
    have hMkOrEq :
        mkOr (singletonAnd y2 ys) (tailOr z zs) =
          eoOr (singletonAnd y2 ys) (tailOr z zs) := by
      unfold mkOr eoOr
      rw [CnfSupport.mk_apply_eq_apply (f := Term.UOp UserOp.or)
        (a := singletonAnd y2 ys) (by simp) hSingletonNe]
      rw [CnfSupport.mk_apply_eq_apply
        (f := Term.Apply (Term.UOp UserOp.or) (singletonAnd y2 ys))
        (a := tailOr z zs) (by simp) hTailOrNe]
    have hMkOrNe : mkOr (singletonAnd y2 ys) (tailOr z zs) ≠ Term.Stuck := by
      rw [hMkOrEq]
      simp [eoOr]
    have hInnerEq :
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.and)
            (mkOr (singletonAnd y2 ys) (tailOr z zs)))
          (Term.Boolean true) =
          eoAnd (eoOr (singletonAnd y2 ys) (tailOr z zs)) (Term.Boolean true) := by
      rw [CnfSupport.mk_apply_eq_apply (f := Term.UOp UserOp.and)
        (a := mkOr (singletonAnd y2 ys) (tailOr z zs)) (by simp) hMkOrNe]
      rw [hMkOrEq]
      rw [CnfSupport.mk_apply_eq_apply
        (f := Term.Apply (Term.UOp UserOp.and)
          (eoOr (singletonAnd y2 ys) (tailOr z zs)))
        (a := Term.Boolean true) (by simp [eoOr]) (by simp)]
    have hRhsEq :
        rhsOrAndDistrib y1 y2 ys z zs =
          eoAnd (eoOr y1 (tailOr z zs))
            (eoAnd (eoOr (singletonAnd y2 ys) (tailOr z zs)) (Term.Boolean true)) := by
      unfold rhsOrAndDistrib
      rw [hInnerEq]
      rw [CnfSupport.mk_apply_eq_apply
        (f := Term.Apply (Term.UOp UserOp.and) (eoOr y1 (tailOr z zs)))
        (a := eoAnd (eoOr (singletonAnd y2 ys) (tailOr z zs)) (Term.Boolean true))
        (by simp [eoOr]) (by simp [eoAnd, eoOr])]
    rw [show __eo_to_smt (lhsOrAndDistrib y1 y2 ys z zs) =
      SmtTerm.or
        (SmtTerm.and (__eo_to_smt y1) (__eo_to_smt (tailAnd y2 ys)))
        (__eo_to_smt (tailOr z zs)) by
      rfl]
    rw [show __eo_to_smt (rhsOrAndDistrib y1 y2 ys z zs) =
      SmtTerm.and
        (SmtTerm.or (__eo_to_smt y1) (__eo_to_smt (tailOr z zs)))
        (SmtTerm.and
          (SmtTerm.or (__eo_to_smt (singletonAnd y2 ys))
            (__eo_to_smt (tailOr z zs)))
          (SmtTerm.Boolean true)) by
      rw [hRhsEq]
      rfl]
    rw [__smtx_model_eval.eq_8, __smtx_model_eval.eq_9, __smtx_model_eval.eq_9,
      __smtx_model_eval.eq_8, __smtx_model_eval.eq_9, __smtx_model_eval.eq_8,
      __smtx_model_eval.eq_1, hEvalY1, hEvalTailAnd, hEvalTailOr, hSingletonEval,
      hEvalTailAnd]
    cases by1 <;> cases bt <;> cases bz <;>
      simp [RuleProofs.smt_value_rel, __smtx_model_eval_eq, __smtx_model_eval_and,
        __smtx_model_eval_or, native_veq, SmtEval.native_and, SmtEval.native_or]

public theorem cmd_step_bool_or_and_distrib_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_or_and_distrib args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bool_or_and_distrib args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_or_and_distrib args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bool_or_and_distrib args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons a2 args =>
          cases args with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons a3 args =>
              cases args with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons a4 args =>
                  cases args with
                  | nil =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | cons a5 args =>
                      cases args with
                      | nil =>
                          cases premises with
                          | nil =>
                              have hATrans :
                                  RuleProofs.eo_has_smt_translation a1 ∧
                                    RuleProofs.eo_has_smt_translation a2 ∧
                                    RuleProofs.eo_has_smt_translation a3 ∧
                                    RuleProofs.eo_has_smt_translation a4 ∧
                                    RuleProofs.eo_has_smt_translation a5 ∧ True := by
                                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                              change __eo_typeof
                                (__eo_prog_bool_or_and_distrib a1 a2 a3 a4 a5) =
                                  Term.Bool at hResultTy
                              refine ⟨?_, ?_⟩
                              · intro _hTrue
                                change eo_interprets M
                                  (__eo_prog_bool_or_and_distrib a1 a2 a3 a4 a5) true
                                exact facts___eo_prog_bool_or_and_distrib_impl M hM
                                  a1 a2 a3 a4 a5 hATrans.1 hATrans.2.1
                                  hATrans.2.2.1 hATrans.2.2.2.1
                                  hATrans.2.2.2.2.1 hResultTy
                              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                  (typed___eo_prog_bool_or_and_distrib_impl
                                    a1 a2 a3 a4 a5 hATrans.1 hATrans.2.1
                                    hATrans.2.2.1 hATrans.2.2.2.1
                                    hATrans.2.2.2.2.1 hResultTy)
                          | cons _ _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                      | cons _ _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
