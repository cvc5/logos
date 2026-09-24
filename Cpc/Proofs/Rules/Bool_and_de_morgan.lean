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

private abbrev eoNot (A : Term) : Term :=
  Term.Apply (Term.UOp UserOp.not) A

private abbrev mkNot (A : Term) : Term :=
  __eo_mk_apply (Term.UOp UserOp.not) A

private abbrev tailAnd (y zs : Term) : Term :=
  eoAnd y zs

private abbrev singletonAnd (y zs : Term) : Term :=
  __eo_list_singleton_elim (Term.UOp UserOp.and) (tailAnd y zs)

private abbrev rhsAndDeMorgan (x y zs : Term) : Term :=
  __eo_mk_apply (Term.Apply (Term.UOp UserOp.or) (eoNot x))
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.or) (mkNot (singletonAnd y zs)))
      (Term.Boolean false))

private abbrev lhsAndDeMorgan (x y zs : Term) : Term :=
  eoNot (eoAnd x (tailAnd y zs))

private theorem prog_bool_and_de_morgan_eq_of_ne_stuck (x y zs : Term) :
    x ≠ Term.Stuck ->
    y ≠ Term.Stuck ->
    zs ≠ Term.Stuck ->
    __eo_prog_bool_and_de_morgan x y zs =
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) (lhsAndDeMorgan x y zs))
        (rhsAndDeMorgan x y zs) := by
  intro hX hY hZs
  cases x <;> cases y <;> cases zs <;>
    simp [__eo_prog_bool_and_de_morgan, lhsAndDeMorgan, rhsAndDeMorgan,
      singletonAnd, tailAnd, eoAnd, mkNot, eoNot] at hX hY hZs ⊢

private theorem typeof_eq_not_left_bool {A B : Term} :
    __eo_typeof_eq (__eo_typeof (eoNot A)) (__eo_typeof B) = Term.Bool ->
    __eo_typeof A = Term.Bool ∧ __eo_typeof B = Term.Bool := by
  intro hTy
  change __eo_typeof_eq (__eo_typeof_not (__eo_typeof A)) (__eo_typeof B) =
    Term.Bool at hTy
  cases hA : __eo_typeof A <;> cases hB : __eo_typeof B <;>
    simp [__eo_typeof_eq, __eo_typeof_not, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not, hA, hB] at hTy ⊢

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

private theorem typeof_mk_not_arg_bool {A : Term} :
    __eo_typeof (mkNot A) = Term.Bool ->
    __eo_typeof A = Term.Bool := by
  intro hTy
  change __eo_typeof (__eo_mk_apply (Term.UOp UserOp.not) A) = Term.Bool at hTy
  by_cases hA : A = Term.Stuck
  · subst A
    change __eo_typeof Term.Stuck = Term.Bool at hTy
    have hBad : __eo_typeof Term.Stuck ≠ Term.Bool := by
      native_decide
    exact False.elim (hBad hTy)
  · rw [CnfSupport.mk_apply_eq_apply (f := Term.UOp UserOp.not) (a := A)
      (by simp) hA] at hTy
    change __eo_typeof_not (__eo_typeof A) = Term.Bool at hTy
    exact CnfSupport.typeof_not_eq_bool hTy

private theorem eo_has_bool_type_mk_not (A : Term) :
    RuleProofs.eo_has_bool_type A ->
    RuleProofs.eo_has_bool_type (mkNot A) := by
  intro hA
  have hANe : A ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type A hA
  change RuleProofs.eo_has_bool_type (__eo_mk_apply (Term.UOp UserOp.not) A)
  rw [CnfSupport.mk_apply_eq_apply (f := Term.UOp UserOp.not) (a := A)
    (by simp) hANe]
  exact RuleProofs.eo_has_bool_type_not_of_bool_arg A hA

private theorem eo_has_bool_type_mk_or_chain
    (A B : Term) :
    RuleProofs.eo_has_bool_type A ->
    RuleProofs.eo_has_bool_type B ->
    RuleProofs.eo_has_bool_type (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.or) A) B) := by
  intro hA hB
  have hANe : A ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type A hA
  rw [CnfSupport.mk_apply_eq_apply (f := Term.UOp UserOp.or) (a := A)
    (by simp) hANe]
  exact eo_has_bool_type_mk_or A B hA hB

private theorem bool_and_de_morgan_data (x y zs : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation zs ->
    __eo_typeof (__eo_prog_bool_and_de_morgan x y zs) = Term.Bool ->
    RuleProofs.eo_has_bool_type x ∧
      RuleProofs.eo_has_bool_type y ∧
      RuleProofs.eo_has_bool_type zs ∧
      CnfSupport.AndList (tailAnd y zs) ∧
      RuleProofs.eo_has_bool_type (singletonAnd y zs) := by
  intro hXTrans hYTrans hZsTrans hResultTy
  have hXNe : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hYNe : y ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hZsNe : zs ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation zs hZsTrans
  have hProgEq := prog_bool_and_de_morgan_eq_of_ne_stuck x y zs hXNe hYNe hZsNe
  have hProgNe : __eo_prog_bool_and_de_morgan x y zs ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  rw [hProgEq] at hProgNe hResultTy
  have hRhsNe : rhsAndDeMorgan x y zs ≠ Term.Stuck :=
    CnfSupport.mk_apply_ne_stuck_right hProgNe
  have hResultTy' :
      __eo_typeof
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) (lhsAndDeMorgan x y zs))
          (rhsAndDeMorgan x y zs)) = Term.Bool := hResultTy
  rw [CnfSupport.mk_apply_eq_apply
    (f := Term.Apply (Term.UOp UserOp.eq) (lhsAndDeMorgan x y zs))
    (a := rhsAndDeMorgan x y zs) (by simp) hRhsNe] at hResultTy'
  change __eo_typeof_eq (__eo_typeof (lhsAndDeMorgan x y zs))
    (__eo_typeof (rhsAndDeMorgan x y zs)) = Term.Bool at hResultTy'
  rcases typeof_eq_not_left_bool (A := eoAnd x (tailAnd y zs))
      (B := rhsAndDeMorgan x y zs) hResultTy' with
    ⟨hLeftArgType, hRhsType⟩
  change __eo_typeof_or (__eo_typeof x) (__eo_typeof (tailAnd y zs)) = Term.Bool
    at hLeftArgType
  have hXType : __eo_typeof x = Term.Bool :=
    CnfSupport.typeof_or_eq_bool_left hLeftArgType
  have hTailType : __eo_typeof (tailAnd y zs) = Term.Bool :=
    CnfSupport.typeof_or_eq_bool_right hLeftArgType
  change __eo_typeof_or (__eo_typeof y) (__eo_typeof zs) = Term.Bool at hTailType
  have hYType : __eo_typeof y = Term.Bool :=
    CnfSupport.typeof_or_eq_bool_left hTailType
  have hZsType : __eo_typeof zs = Term.Bool :=
    CnfSupport.typeof_or_eq_bool_right hTailType
  have hInnerType :
      __eo_typeof
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.or) (mkNot (singletonAnd y zs)))
          (Term.Boolean false)) = Term.Bool :=
    CnfSupport.typeof_mk_apply_or_right_bool hRhsType
  have hInnerNe :
      __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.or) (mkNot (singletonAnd y zs)))
        (Term.Boolean false) ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hInnerType
  have hInnerFnNe :
      __eo_mk_apply (Term.UOp UserOp.or) (mkNot (singletonAnd y zs)) ≠
        Term.Stuck :=
    CnfSupport.mk_apply_ne_stuck_left hInnerNe
  have hMkNotNe : mkNot (singletonAnd y zs) ≠ Term.Stuck :=
    CnfSupport.mk_apply_ne_stuck_right hInnerFnNe
  have hInnerType' := hInnerType
  rw [CnfSupport.mk_apply_eq_apply (f := Term.UOp UserOp.or)
    (a := mkNot (singletonAnd y zs)) (by simp) hMkNotNe] at hInnerType'
  have hNotSingletonType : __eo_typeof (mkNot (singletonAnd y zs)) = Term.Bool :=
    CnfSupport.typeof_mk_apply_or_left_bool hInnerType'
  have hSingletonType : __eo_typeof (singletonAnd y zs) = Term.Bool :=
    typeof_mk_not_arg_bool hNotSingletonType
  have hSingletonNe : singletonAnd y zs ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hSingletonType
  have hTailList : CnfSupport.AndList (tailAnd y zs) :=
    CnfSupport.andList_of_singleton_elim_ne_stuck hSingletonNe
  have hXBool : RuleProofs.eo_has_bool_type x :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x Term.Bool (__eo_to_smt x) rfl hXTrans hXType
  have hYBool : RuleProofs.eo_has_bool_type y :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      y Term.Bool (__eo_to_smt y) rfl hYTrans hYType
  have hZsBool : RuleProofs.eo_has_bool_type zs :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      zs Term.Bool (__eo_to_smt zs) rfl hZsTrans hZsType
  have hTailBool : RuleProofs.eo_has_bool_type (tailAnd y zs) :=
    RuleProofs.eo_has_bool_type_and_of_bool_args y zs hYBool hZsBool
  have hSingletonBool : RuleProofs.eo_has_bool_type (singletonAnd y zs) :=
    CnfSupport.andList_singleton_elim_preserves_bool_type hTailList hTailBool
  exact ⟨hXBool, hYBool, hZsBool, hTailList, hSingletonBool⟩

private theorem typed___eo_prog_bool_and_de_morgan_impl (x y zs : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation zs ->
    __eo_typeof (__eo_prog_bool_and_de_morgan x y zs) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__eo_prog_bool_and_de_morgan x y zs) := by
  intro hXTrans hYTrans hZsTrans hResultTy
  have hXNe : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hYNe : y ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hZsNe : zs ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation zs hZsTrans
  rcases bool_and_de_morgan_data x y zs hXTrans hYTrans hZsTrans hResultTy with
    ⟨hXBool, hYBool, hZsBool, hTailList, hSingletonBool⟩
  have hTailBool : RuleProofs.eo_has_bool_type (tailAnd y zs) :=
    RuleProofs.eo_has_bool_type_and_of_bool_args y zs hYBool hZsBool
  have hAndBool : RuleProofs.eo_has_bool_type (eoAnd x (tailAnd y zs)) :=
    RuleProofs.eo_has_bool_type_and_of_bool_args x (tailAnd y zs) hXBool hTailBool
  have hLeftBool : RuleProofs.eo_has_bool_type (lhsAndDeMorgan x y zs) :=
    RuleProofs.eo_has_bool_type_not_of_bool_arg (eoAnd x (tailAnd y zs)) hAndBool
  have hNotXBool : RuleProofs.eo_has_bool_type (eoNot x) :=
    RuleProofs.eo_has_bool_type_not_of_bool_arg x hXBool
  have hNotSingletonBool : RuleProofs.eo_has_bool_type (mkNot (singletonAnd y zs)) :=
    eo_has_bool_type_mk_not (singletonAnd y zs) hSingletonBool
  have hInnerBool :
      RuleProofs.eo_has_bool_type
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.or) (mkNot (singletonAnd y zs)))
          (Term.Boolean false)) :=
    eo_has_bool_type_mk_or_chain (mkNot (singletonAnd y zs)) (Term.Boolean false)
      hNotSingletonBool RuleProofs.eo_has_bool_type_false
  have hRhsBool : RuleProofs.eo_has_bool_type (rhsAndDeMorgan x y zs) :=
    eo_has_bool_type_mk_or (eoNot x)
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.or) (mkNot (singletonAnd y zs)))
        (Term.Boolean false))
      hNotXBool hInnerBool
  have hProgEq := prog_bool_and_de_morgan_eq_of_ne_stuck x y zs hXNe hYNe hZsNe
  rw [hProgEq]
  have hRhsNe : rhsAndDeMorgan x y zs ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type _ hRhsBool
  rw [CnfSupport.mk_apply_eq_apply
    (f := Term.Apply (Term.UOp UserOp.eq) (lhsAndDeMorgan x y zs))
    (a := rhsAndDeMorgan x y zs) (by simp) hRhsNe]
  exact CnfSupport.eo_has_bool_type_eq_of_bool_args
    (lhsAndDeMorgan x y zs) (rhsAndDeMorgan x y zs) hLeftBool hRhsBool

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

private theorem facts___eo_prog_bool_and_de_morgan_impl
    (M : SmtModel) (hM : model_wf M) (x y zs : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation zs ->
    __eo_typeof (__eo_prog_bool_and_de_morgan x y zs) = Term.Bool ->
    eo_interprets M (__eo_prog_bool_and_de_morgan x y zs) true := by
  intro hXTrans hYTrans hZsTrans hResultTy
  have hXNe : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hYNe : y ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hZsNe : zs ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation zs hZsTrans
  rcases bool_and_de_morgan_data x y zs hXTrans hYTrans hZsTrans hResultTy with
    ⟨hXBool, hYBool, hZsBool, hTailList, hSingletonBool⟩
  have hTailBool : RuleProofs.eo_has_bool_type (tailAnd y zs) :=
    RuleProofs.eo_has_bool_type_and_of_bool_args y zs hYBool hZsBool
  have hAndBool : RuleProofs.eo_has_bool_type (eoAnd x (tailAnd y zs)) :=
    RuleProofs.eo_has_bool_type_and_of_bool_args x (tailAnd y zs) hXBool hTailBool
  have hLeftBool : RuleProofs.eo_has_bool_type (lhsAndDeMorgan x y zs) :=
    RuleProofs.eo_has_bool_type_not_of_bool_arg (eoAnd x (tailAnd y zs)) hAndBool
  have hProgBool :
      RuleProofs.eo_has_bool_type (__eo_prog_bool_and_de_morgan x y zs) :=
    typed___eo_prog_bool_and_de_morgan_impl x y zs hXTrans hYTrans hZsTrans hResultTy
  have hProgEq := prog_bool_and_de_morgan_eq_of_ne_stuck x y zs hXNe hYNe hZsNe
  rw [hProgEq]
  have hNotXBool : RuleProofs.eo_has_bool_type (eoNot x) :=
    RuleProofs.eo_has_bool_type_not_of_bool_arg x hXBool
  have hNotSingletonBool : RuleProofs.eo_has_bool_type (mkNot (singletonAnd y zs)) :=
    eo_has_bool_type_mk_not (singletonAnd y zs) hSingletonBool
  have hInnerBool :
      RuleProofs.eo_has_bool_type
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.or) (mkNot (singletonAnd y zs)))
          (Term.Boolean false)) :=
    eo_has_bool_type_mk_or_chain (mkNot (singletonAnd y zs)) (Term.Boolean false)
      hNotSingletonBool RuleProofs.eo_has_bool_type_false
  have hRhsBool : RuleProofs.eo_has_bool_type (rhsAndDeMorgan x y zs) :=
    eo_has_bool_type_mk_or (eoNot x)
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.or) (mkNot (singletonAnd y zs)))
        (Term.Boolean false))
      hNotXBool hInnerBool
  have hRhsNe : rhsAndDeMorgan x y zs ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type _ hRhsBool
  rw [CnfSupport.mk_apply_eq_apply
    (f := Term.Apply (Term.UOp UserOp.eq) (lhsAndDeMorgan x y zs))
    (a := rhsAndDeMorgan x y zs) (by simp) hRhsNe]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [hProgEq, CnfSupport.mk_apply_eq_apply
      (f := Term.Apply (Term.UOp UserOp.eq) (lhsAndDeMorgan x y zs))
      (a := rhsAndDeMorgan x y zs) (by simp) hRhsNe] using hProgBool
  · rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM x hXBool with
      ⟨bx, hEvalX⟩
    rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM
        (tailAnd y zs) hTailBool with
      ⟨bt, hEvalTail⟩
    have hSingletonEval :
        __smtx_model_eval M (__eo_to_smt (singletonAnd y zs)) =
          __smtx_model_eval M (__eo_to_smt (tailAnd y zs)) :=
      bool_eval_eq_of_true_iff M hM (singletonAnd y zs) (tailAnd y zs)
        hSingletonBool hTailBool
        (CnfSupport.andList_singleton_elim_true_iff M hTailList hTailBool)
    have hSingletonNe : singletonAnd y zs ≠ Term.Stuck :=
      RuleProofs.term_ne_stuck_of_has_bool_type _ hSingletonBool
    have hMkNotEq : mkNot (singletonAnd y zs) = eoNot (singletonAnd y zs) :=
      CnfSupport.mk_apply_eq_apply (f := Term.UOp UserOp.not)
        (a := singletonAnd y zs) (by simp) hSingletonNe
    have hMkNotNe : mkNot (singletonAnd y zs) ≠ Term.Stuck := by
      rw [hMkNotEq]
      simp [eoNot]
    have hInnerEq :
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.or) (mkNot (singletonAnd y zs)))
          (Term.Boolean false) =
          eoOr (eoNot (singletonAnd y zs)) (Term.Boolean false) := by
      rw [CnfSupport.mk_apply_eq_apply (f := Term.UOp UserOp.or)
        (a := mkNot (singletonAnd y zs)) (by simp) hMkNotNe]
      rw [hMkNotEq]
      rw [CnfSupport.mk_apply_eq_apply
        (f := Term.Apply (Term.UOp UserOp.or) (eoNot (singletonAnd y zs)))
        (a := Term.Boolean false) (by simp [eoNot]) (by simp)]
    have hRhsEq :
        rhsAndDeMorgan x y zs =
          eoOr (eoNot x)
            (eoOr (eoNot (singletonAnd y zs)) (Term.Boolean false)) := by
      unfold rhsAndDeMorgan
      rw [hInnerEq]
      rw [CnfSupport.mk_apply_eq_apply
        (f := Term.Apply (Term.UOp UserOp.or) (eoNot x))
        (a := eoOr (eoNot (singletonAnd y zs)) (Term.Boolean false))
        (by simp [eoNot]) (by simp [eoOr, eoNot])]
    rw [show __eo_to_smt (lhsAndDeMorgan x y zs) =
      SmtTerm.not (SmtTerm.and (__eo_to_smt x) (__eo_to_smt (tailAnd y zs))) by
      rfl]
    rw [show __eo_to_smt (rhsAndDeMorgan x y zs) =
      SmtTerm.or (SmtTerm.not (__eo_to_smt x))
        (SmtTerm.or (SmtTerm.not (__eo_to_smt (singletonAnd y zs)))
          (SmtTerm.Boolean false)) by
      rw [hRhsEq]
      rfl]
    rw [__smtx_model_eval.eq_7, __smtx_model_eval.eq_9, __smtx_model_eval.eq_8,
      __smtx_model_eval.eq_7, __smtx_model_eval.eq_8, __smtx_model_eval.eq_7,
      __smtx_model_eval.eq_1, hEvalX, hEvalTail, hSingletonEval, hEvalTail]
    cases bx <;> cases bt <;>
      simp [RuleProofs.smt_value_rel, __smtx_model_eval_eq, __smtx_model_eval_and,
        __smtx_model_eval_or, __smtx_model_eval_not, native_veq, SmtEval.native_and,
        SmtEval.native_or, SmtEval.native_not]

public theorem cmd_step_bool_and_de_morgan_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_and_de_morgan args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bool_and_de_morgan args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_and_de_morgan args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bool_and_de_morgan args premises ≠ Term.Stuck :=
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
                  cases premises with
                  | nil =>
                      have hATrans :
                          RuleProofs.eo_has_smt_translation a1 ∧
                            RuleProofs.eo_has_smt_translation a2 ∧
                            RuleProofs.eo_has_smt_translation a3 ∧ True := by
                        simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                      change __eo_typeof (__eo_prog_bool_and_de_morgan a1 a2 a3) =
                        Term.Bool at hResultTy
                      refine ⟨?_, ?_⟩
                      · intro _hTrue
                        change eo_interprets M (__eo_prog_bool_and_de_morgan a1 a2 a3) true
                        exact facts___eo_prog_bool_and_de_morgan_impl M hM a1 a2 a3
                          hATrans.1 hATrans.2.1 hATrans.2.2.1 hResultTy
                      · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                          (typed___eo_prog_bool_and_de_morgan_impl a1 a2 a3
                            hATrans.1 hATrans.2.1 hATrans.2.2.1 hResultTy)
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
