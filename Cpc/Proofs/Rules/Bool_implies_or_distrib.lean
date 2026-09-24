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

private abbrev eoImp (A B : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B

private abbrev mkImp (A B : Term) : Term :=
  __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.imp) A) B

private abbrev tailOr (y ys : Term) : Term :=
  eoOr y ys

private abbrev singletonOr (y ys : Term) : Term :=
  __eo_list_singleton_elim (Term.UOp UserOp.or) (tailOr y ys)

private abbrev lhsImpliesOrDistrib (y1 y2 ys z : Term) : Term :=
  eoImp (eoOr y1 (tailOr y2 ys)) z

private abbrev rhsImpliesOrDistrib (y1 y2 ys z : Term) : Term :=
  __eo_mk_apply (Term.Apply (Term.UOp UserOp.and) (eoImp y1 z))
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.and) (mkImp (singletonOr y2 ys) z))
      (Term.Boolean true))

private theorem prog_bool_implies_or_distrib_eq_of_ne_stuck (y1 y2 ys z : Term) :
    y1 ≠ Term.Stuck ->
    y2 ≠ Term.Stuck ->
    ys ≠ Term.Stuck ->
    z ≠ Term.Stuck ->
    __eo_prog_bool_implies_or_distrib y1 y2 ys z =
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq)
        (lhsImpliesOrDistrib y1 y2 ys z))
        (rhsImpliesOrDistrib y1 y2 ys z) := by
  intro hY1 hY2 hYs hZ
  simp [__eo_prog_bool_implies_or_distrib, lhsImpliesOrDistrib,
    rhsImpliesOrDistrib, singletonOr, tailOr, mkImp, eoImp]

private theorem typeof_eq_imp_left_bool {A B C : Term} :
    __eo_typeof_eq (__eo_typeof (eoImp A B)) (__eo_typeof C) = Term.Bool ->
    __eo_typeof A = Term.Bool ∧ __eo_typeof B = Term.Bool ∧
      __eo_typeof C = Term.Bool := by
  intro hTy
  change __eo_typeof_eq (__eo_typeof_or (__eo_typeof A) (__eo_typeof B))
    (__eo_typeof C) = Term.Bool at hTy
  cases hA : __eo_typeof A <;> cases hB : __eo_typeof B <;>
    cases hC : __eo_typeof C <;>
    simp [__eo_typeof_eq, __eo_typeof_or, __eo_requires, __eo_eq,
      native_ite, native_teq, native_not, hA, hB, hC] at hTy ⊢

private theorem typeof_mk_imp_left_bool {A B : Term} :
    __eo_typeof (mkImp A B) = Term.Bool ->
    __eo_typeof A = Term.Bool := by
  intro hTy
  change __eo_typeof (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.imp) A) B) =
    Term.Bool at hTy
  have hOuterNe :
      __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.imp) A) B ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  have hFnNe : __eo_mk_apply (Term.UOp UserOp.imp) A ≠ Term.Stuck :=
    CnfSupport.mk_apply_ne_stuck_left hOuterNe
  have hANe : A ≠ Term.Stuck :=
    CnfSupport.mk_apply_ne_stuck_right hFnNe
  have hFnEq :
      __eo_mk_apply (Term.UOp UserOp.imp) A =
        Term.Apply (Term.UOp UserOp.imp) A :=
    CnfSupport.mk_apply_eq_apply (f := Term.UOp UserOp.imp) (a := A)
      (by simp) hANe
  have hOuterNe' :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.imp) A) B ≠ Term.Stuck := by
    simpa [hFnEq] using hOuterNe
  have hBNe : B ≠ Term.Stuck :=
    CnfSupport.mk_apply_ne_stuck_right hOuterNe'
  have hTy' := hTy
  rw [hFnEq] at hTy'
  rw [CnfSupport.mk_apply_eq_apply
    (f := Term.Apply (Term.UOp UserOp.imp) A) (a := B)
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

private theorem eo_has_bool_type_mk_imp
    (A B : Term) :
    RuleProofs.eo_has_bool_type A ->
    RuleProofs.eo_has_bool_type B ->
    RuleProofs.eo_has_bool_type (__eo_mk_apply (Term.Apply (Term.UOp UserOp.imp) A) B) := by
  intro hA hB
  have hBNe : B ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type B hB
  rw [CnfSupport.mk_apply_eq_apply (f := Term.Apply (Term.UOp UserOp.imp) A)
    (a := B) (by simp) hBNe]
  exact CnfSupport.eo_has_bool_type_imp_of_bool_args A B hA hB

private theorem eo_has_bool_type_mk_imp_chain
    (A B : Term) :
    RuleProofs.eo_has_bool_type A ->
    RuleProofs.eo_has_bool_type B ->
    RuleProofs.eo_has_bool_type (mkImp A B) := by
  intro hA hB
  have hANe : A ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type A hA
  change RuleProofs.eo_has_bool_type
    (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.imp) A) B)
  rw [CnfSupport.mk_apply_eq_apply (f := Term.UOp UserOp.imp) (a := A)
    (by simp) hANe]
  exact eo_has_bool_type_mk_imp A B hA hB

private theorem bool_implies_or_distrib_data (y1 y2 ys z : Term) :
    RuleProofs.eo_has_smt_translation y1 ->
    RuleProofs.eo_has_smt_translation y2 ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation z ->
    __eo_typeof (__eo_prog_bool_implies_or_distrib y1 y2 ys z) = Term.Bool ->
    RuleProofs.eo_has_bool_type y1 ∧
      RuleProofs.eo_has_bool_type y2 ∧
      RuleProofs.eo_has_bool_type ys ∧
      RuleProofs.eo_has_bool_type z ∧
      CnfSupport.OrList (tailOr y2 ys) ∧
      RuleProofs.eo_has_bool_type (singletonOr y2 ys) := by
  intro hY1Trans hY2Trans hYsTrans hZTrans hResultTy
  have hY1Ne : y1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y1 hY1Trans
  have hY2Ne : y2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y2 hY2Trans
  have hYsNe : ys ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation ys hYsTrans
  have hZNe : z ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation z hZTrans
  have hProgEq :=
    prog_bool_implies_or_distrib_eq_of_ne_stuck y1 y2 ys z hY1Ne hY2Ne hYsNe hZNe
  have hProgNe : __eo_prog_bool_implies_or_distrib y1 y2 ys z ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  rw [hProgEq] at hProgNe hResultTy
  have hRhsNe : rhsImpliesOrDistrib y1 y2 ys z ≠ Term.Stuck :=
    CnfSupport.mk_apply_ne_stuck_right hProgNe
  have hResultTy' :
      __eo_typeof
        (__eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq) (lhsImpliesOrDistrib y1 y2 ys z))
          (rhsImpliesOrDistrib y1 y2 ys z)) = Term.Bool := hResultTy
  rw [CnfSupport.mk_apply_eq_apply
    (f := Term.Apply (Term.UOp UserOp.eq) (lhsImpliesOrDistrib y1 y2 ys z))
    (a := rhsImpliesOrDistrib y1 y2 ys z) (by simp) hRhsNe] at hResultTy'
  change __eo_typeof_eq (__eo_typeof (lhsImpliesOrDistrib y1 y2 ys z))
    (__eo_typeof (rhsImpliesOrDistrib y1 y2 ys z)) = Term.Bool at hResultTy'
  rcases typeof_eq_imp_left_bool (A := eoOr y1 (tailOr y2 ys)) (B := z)
      (C := rhsImpliesOrDistrib y1 y2 ys z) hResultTy' with
    ⟨hLeftArgType, hZType, hRhsType⟩
  change __eo_typeof_or (__eo_typeof y1) (__eo_typeof (tailOr y2 ys)) =
    Term.Bool at hLeftArgType
  have hY1Type : __eo_typeof y1 = Term.Bool :=
    CnfSupport.typeof_or_eq_bool_left hLeftArgType
  have hTailType : __eo_typeof (tailOr y2 ys) = Term.Bool :=
    CnfSupport.typeof_or_eq_bool_right hLeftArgType
  change __eo_typeof_or (__eo_typeof y2) (__eo_typeof ys) = Term.Bool at hTailType
  have hY2Type : __eo_typeof y2 = Term.Bool :=
    CnfSupport.typeof_or_eq_bool_left hTailType
  have hYsType : __eo_typeof ys = Term.Bool :=
    CnfSupport.typeof_or_eq_bool_right hTailType
  have hInnerType :
      __eo_typeof
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.and) (mkImp (singletonOr y2 ys) z))
          (Term.Boolean true)) = Term.Bool :=
    CnfSupport.typeof_mk_apply_and_right_bool hRhsType
  have hInnerNe :
      __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.and) (mkImp (singletonOr y2 ys) z))
        (Term.Boolean true) ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hInnerType
  have hInnerFnNe :
      __eo_mk_apply (Term.UOp UserOp.and) (mkImp (singletonOr y2 ys) z) ≠
        Term.Stuck :=
    CnfSupport.mk_apply_ne_stuck_left hInnerNe
  have hMkImpNe : mkImp (singletonOr y2 ys) z ≠ Term.Stuck :=
    CnfSupport.mk_apply_ne_stuck_right hInnerFnNe
  have hInnerType' := hInnerType
  rw [CnfSupport.mk_apply_eq_apply (f := Term.UOp UserOp.and)
    (a := mkImp (singletonOr y2 ys) z) (by simp) hMkImpNe] at hInnerType'
  have hMkImpType : __eo_typeof (mkImp (singletonOr y2 ys) z) = Term.Bool :=
    CnfSupport.typeof_mk_apply_and_left_bool hInnerType'
  have hSingletonType : __eo_typeof (singletonOr y2 ys) = Term.Bool :=
    typeof_mk_imp_left_bool hMkImpType
  have hSingletonNe : singletonOr y2 ys ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hSingletonType
  have hTailList : CnfSupport.OrList (tailOr y2 ys) :=
    CnfSupport.orList_of_singleton_elim_ne_stuck hSingletonNe
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
  have hTailBool : RuleProofs.eo_has_bool_type (tailOr y2 ys) :=
    RuleProofs.eo_has_bool_type_or_of_bool_args y2 ys hY2Bool hYsBool
  have hSingletonBool : RuleProofs.eo_has_bool_type (singletonOr y2 ys) :=
    CnfSupport.orList_singleton_elim_preserves_bool_type hTailList hTailBool
  exact ⟨hY1Bool, hY2Bool, hYsBool, hZBool, hTailList, hSingletonBool⟩

private theorem typed___eo_prog_bool_implies_or_distrib_impl (y1 y2 ys z : Term) :
    RuleProofs.eo_has_smt_translation y1 ->
    RuleProofs.eo_has_smt_translation y2 ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation z ->
    __eo_typeof (__eo_prog_bool_implies_or_distrib y1 y2 ys z) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__eo_prog_bool_implies_or_distrib y1 y2 ys z) := by
  intro hY1Trans hY2Trans hYsTrans hZTrans hResultTy
  have hY1Ne : y1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y1 hY1Trans
  have hY2Ne : y2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y2 hY2Trans
  have hYsNe : ys ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation ys hYsTrans
  have hZNe : z ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation z hZTrans
  rcases bool_implies_or_distrib_data y1 y2 ys z hY1Trans hY2Trans hYsTrans hZTrans
      hResultTy with
    ⟨hY1Bool, hY2Bool, hYsBool, hZBool, hTailList, hSingletonBool⟩
  have hTailBool : RuleProofs.eo_has_bool_type (tailOr y2 ys) :=
    RuleProofs.eo_has_bool_type_or_of_bool_args y2 ys hY2Bool hYsBool
  have hOrBool : RuleProofs.eo_has_bool_type (eoOr y1 (tailOr y2 ys)) :=
    RuleProofs.eo_has_bool_type_or_of_bool_args y1 (tailOr y2 ys) hY1Bool hTailBool
  have hLeftBool : RuleProofs.eo_has_bool_type (lhsImpliesOrDistrib y1 y2 ys z) :=
    CnfSupport.eo_has_bool_type_imp_of_bool_args (eoOr y1 (tailOr y2 ys)) z
      hOrBool hZBool
  have hY1ImpBool : RuleProofs.eo_has_bool_type (eoImp y1 z) :=
    CnfSupport.eo_has_bool_type_imp_of_bool_args y1 z hY1Bool hZBool
  have hSingletonImpBool : RuleProofs.eo_has_bool_type (mkImp (singletonOr y2 ys) z) :=
    eo_has_bool_type_mk_imp_chain (singletonOr y2 ys) z hSingletonBool hZBool
  have hInnerBool :
      RuleProofs.eo_has_bool_type
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.and) (mkImp (singletonOr y2 ys) z))
          (Term.Boolean true)) :=
    eo_has_bool_type_mk_and_chain (mkImp (singletonOr y2 ys) z) (Term.Boolean true)
      hSingletonImpBool RuleProofs.eo_has_bool_type_true
  have hRhsBool : RuleProofs.eo_has_bool_type (rhsImpliesOrDistrib y1 y2 ys z) :=
    eo_has_bool_type_mk_and (eoImp y1 z)
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.and) (mkImp (singletonOr y2 ys) z))
        (Term.Boolean true))
      hY1ImpBool hInnerBool
  have hProgEq :=
    prog_bool_implies_or_distrib_eq_of_ne_stuck y1 y2 ys z hY1Ne hY2Ne hYsNe hZNe
  rw [hProgEq]
  have hRhsNe : rhsImpliesOrDistrib y1 y2 ys z ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type _ hRhsBool
  rw [CnfSupport.mk_apply_eq_apply
    (f := Term.Apply (Term.UOp UserOp.eq) (lhsImpliesOrDistrib y1 y2 ys z))
    (a := rhsImpliesOrDistrib y1 y2 ys z) (by simp) hRhsNe]
  exact CnfSupport.eo_has_bool_type_eq_of_bool_args
    (lhsImpliesOrDistrib y1 y2 ys z) (rhsImpliesOrDistrib y1 y2 ys z)
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

private theorem facts___eo_prog_bool_implies_or_distrib_impl
    (M : SmtModel) (hM : model_wf M) (y1 y2 ys z : Term) :
    RuleProofs.eo_has_smt_translation y1 ->
    RuleProofs.eo_has_smt_translation y2 ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation z ->
    __eo_typeof (__eo_prog_bool_implies_or_distrib y1 y2 ys z) = Term.Bool ->
    eo_interprets M (__eo_prog_bool_implies_or_distrib y1 y2 ys z) true := by
  intro hY1Trans hY2Trans hYsTrans hZTrans hResultTy
  have hY1Ne : y1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y1 hY1Trans
  have hY2Ne : y2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y2 hY2Trans
  have hYsNe : ys ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation ys hYsTrans
  have hZNe : z ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation z hZTrans
  rcases bool_implies_or_distrib_data y1 y2 ys z hY1Trans hY2Trans hYsTrans hZTrans
      hResultTy with
    ⟨hY1Bool, hY2Bool, hYsBool, hZBool, hTailList, hSingletonBool⟩
  have hTailBool : RuleProofs.eo_has_bool_type (tailOr y2 ys) :=
    RuleProofs.eo_has_bool_type_or_of_bool_args y2 ys hY2Bool hYsBool
  have hOrBool : RuleProofs.eo_has_bool_type (eoOr y1 (tailOr y2 ys)) :=
    RuleProofs.eo_has_bool_type_or_of_bool_args y1 (tailOr y2 ys) hY1Bool hTailBool
  have hLeftBool : RuleProofs.eo_has_bool_type (lhsImpliesOrDistrib y1 y2 ys z) :=
    CnfSupport.eo_has_bool_type_imp_of_bool_args (eoOr y1 (tailOr y2 ys)) z
      hOrBool hZBool
  have hProgBool :
      RuleProofs.eo_has_bool_type (__eo_prog_bool_implies_or_distrib y1 y2 ys z) :=
    typed___eo_prog_bool_implies_or_distrib_impl y1 y2 ys z
      hY1Trans hY2Trans hYsTrans hZTrans hResultTy
  have hProgEq :=
    prog_bool_implies_or_distrib_eq_of_ne_stuck y1 y2 ys z hY1Ne hY2Ne hYsNe hZNe
  rw [hProgEq]
  have hY1ImpBool : RuleProofs.eo_has_bool_type (eoImp y1 z) :=
    CnfSupport.eo_has_bool_type_imp_of_bool_args y1 z hY1Bool hZBool
  have hSingletonImpBool : RuleProofs.eo_has_bool_type (mkImp (singletonOr y2 ys) z) :=
    eo_has_bool_type_mk_imp_chain (singletonOr y2 ys) z hSingletonBool hZBool
  have hInnerBool :
      RuleProofs.eo_has_bool_type
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.and) (mkImp (singletonOr y2 ys) z))
          (Term.Boolean true)) :=
    eo_has_bool_type_mk_and_chain (mkImp (singletonOr y2 ys) z) (Term.Boolean true)
      hSingletonImpBool RuleProofs.eo_has_bool_type_true
  have hRhsBool : RuleProofs.eo_has_bool_type (rhsImpliesOrDistrib y1 y2 ys z) :=
    eo_has_bool_type_mk_and (eoImp y1 z)
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.and) (mkImp (singletonOr y2 ys) z))
        (Term.Boolean true))
      hY1ImpBool hInnerBool
  have hRhsNe : rhsImpliesOrDistrib y1 y2 ys z ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type _ hRhsBool
  rw [CnfSupport.mk_apply_eq_apply
    (f := Term.Apply (Term.UOp UserOp.eq) (lhsImpliesOrDistrib y1 y2 ys z))
    (a := rhsImpliesOrDistrib y1 y2 ys z) (by simp) hRhsNe]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [hProgEq, CnfSupport.mk_apply_eq_apply
      (f := Term.Apply (Term.UOp UserOp.eq) (lhsImpliesOrDistrib y1 y2 ys z))
      (a := rhsImpliesOrDistrib y1 y2 ys z) (by simp) hRhsNe] using hProgBool
  · rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM y1 hY1Bool with
      ⟨by1, hEvalY1⟩
    rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM
        (tailOr y2 ys) hTailBool with
      ⟨bt, hEvalTail⟩
    rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM z hZBool with
      ⟨bz, hEvalZ⟩
    have hSingletonEval :
        __smtx_model_eval M (__eo_to_smt (singletonOr y2 ys)) =
          __smtx_model_eval M (__eo_to_smt (tailOr y2 ys)) :=
      bool_eval_eq_of_true_iff M hM (singletonOr y2 ys) (tailOr y2 ys)
        hSingletonBool hTailBool
        (CnfSupport.orList_singleton_elim_true_iff M hM hTailList hTailBool)
    have hSingletonNe : singletonOr y2 ys ≠ Term.Stuck :=
      RuleProofs.term_ne_stuck_of_has_bool_type _ hSingletonBool
    have hMkImpEq : mkImp (singletonOr y2 ys) z = eoImp (singletonOr y2 ys) z := by
      unfold mkImp eoImp
      rw [CnfSupport.mk_apply_eq_apply (f := Term.UOp UserOp.imp)
        (a := singletonOr y2 ys) (by simp) hSingletonNe]
      rw [CnfSupport.mk_apply_eq_apply
        (f := Term.Apply (Term.UOp UserOp.imp) (singletonOr y2 ys))
        (a := z) (by simp) hZNe]
    have hMkImpNe : mkImp (singletonOr y2 ys) z ≠ Term.Stuck := by
      rw [hMkImpEq]
      simp [eoImp]
    have hInnerEq :
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.and) (mkImp (singletonOr y2 ys) z))
          (Term.Boolean true) =
          eoAnd (eoImp (singletonOr y2 ys) z) (Term.Boolean true) := by
      rw [CnfSupport.mk_apply_eq_apply (f := Term.UOp UserOp.and)
        (a := mkImp (singletonOr y2 ys) z) (by simp) hMkImpNe]
      rw [hMkImpEq]
      rw [CnfSupport.mk_apply_eq_apply
        (f := Term.Apply (Term.UOp UserOp.and) (eoImp (singletonOr y2 ys) z))
        (a := Term.Boolean true) (by simp [eoImp]) (by simp)]
    have hRhsEq :
        rhsImpliesOrDistrib y1 y2 ys z =
          eoAnd (eoImp y1 z)
            (eoAnd (eoImp (singletonOr y2 ys) z) (Term.Boolean true)) := by
      unfold rhsImpliesOrDistrib
      rw [hInnerEq]
      rw [CnfSupport.mk_apply_eq_apply
        (f := Term.Apply (Term.UOp UserOp.and) (eoImp y1 z))
        (a := eoAnd (eoImp (singletonOr y2 ys) z) (Term.Boolean true))
        (by simp [eoImp]) (by simp [eoAnd, eoImp])]
    rw [show __eo_to_smt (lhsImpliesOrDistrib y1 y2 ys z) =
      SmtTerm.imp
        (SmtTerm.or (__eo_to_smt y1) (__eo_to_smt (tailOr y2 ys)))
        (__eo_to_smt z) by
      rfl]
    rw [show __eo_to_smt (rhsImpliesOrDistrib y1 y2 ys z) =
      SmtTerm.and (SmtTerm.imp (__eo_to_smt y1) (__eo_to_smt z))
        (SmtTerm.and
          (SmtTerm.imp (__eo_to_smt (singletonOr y2 ys)) (__eo_to_smt z))
          (SmtTerm.Boolean true)) by
      rw [hRhsEq]
      rfl]
    rw [__smtx_model_eval.eq_10, __smtx_model_eval.eq_8, __smtx_model_eval.eq_9,
      __smtx_model_eval.eq_10, __smtx_model_eval.eq_9, __smtx_model_eval.eq_10,
      __smtx_model_eval.eq_1, hEvalY1, hEvalTail, hEvalZ, hSingletonEval, hEvalTail]
    cases by1 <;> cases bt <;> cases bz <;>
      simp [RuleProofs.smt_value_rel, __smtx_model_eval_eq, __smtx_model_eval_and,
        __smtx_model_eval_imp, __smtx_model_eval_or, __smtx_model_eval_not,
        native_veq, SmtEval.native_and, SmtEval.native_or, SmtEval.native_not]

public theorem cmd_step_bool_implies_or_distrib_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_implies_or_distrib args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bool_implies_or_distrib args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_implies_or_distrib args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bool_implies_or_distrib args premises ≠ Term.Stuck :=
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
                      cases premises with
                      | nil =>
                          have hATrans :
                              RuleProofs.eo_has_smt_translation a1 ∧
                                RuleProofs.eo_has_smt_translation a2 ∧
                                RuleProofs.eo_has_smt_translation a3 ∧
                                RuleProofs.eo_has_smt_translation a4 ∧ True := by
                            simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                          change __eo_typeof
                            (__eo_prog_bool_implies_or_distrib a1 a2 a3 a4) =
                              Term.Bool at hResultTy
                          refine ⟨?_, ?_⟩
                          · intro _hTrue
                            change eo_interprets M
                              (__eo_prog_bool_implies_or_distrib a1 a2 a3 a4) true
                            exact facts___eo_prog_bool_implies_or_distrib_impl M hM
                              a1 a2 a3 a4 hATrans.1 hATrans.2.1 hATrans.2.2.1
                              hATrans.2.2.2.1 hResultTy
                          · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                              (typed___eo_prog_bool_implies_or_distrib_impl a1 a2 a3 a4
                                hATrans.1 hATrans.2.1 hATrans.2.2.1
                                hATrans.2.2.2.1 hResultTy)
                      | cons _ _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
