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

private abbrev tailOr (y zs : Term) : Term :=
  eoOr y zs

private abbrev singletonOr (y zs : Term) : Term :=
  __eo_list_singleton_elim (Term.UOp UserOp.or) (tailOr y zs)

private abbrev rhsOrDeMorgan (x y zs : Term) : Term :=
  __eo_mk_apply (Term.Apply (Term.UOp UserOp.and) (eoNot x))
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.and) (mkNot (singletonOr y zs)))
      (Term.Boolean true))

private abbrev lhsOrDeMorgan (x y zs : Term) : Term :=
  eoNot (eoOr x (tailOr y zs))

private theorem prog_bool_or_de_morgan_eq_of_ne_stuck (x y zs : Term) :
    x ≠ Term.Stuck ->
    y ≠ Term.Stuck ->
    zs ≠ Term.Stuck ->
    __eo_prog_bool_or_de_morgan x y zs =
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) (lhsOrDeMorgan x y zs))
        (rhsOrDeMorgan x y zs) := by
  intro hX hY hZs
  cases x <;> cases y <;> cases zs <;>
    simp [__eo_prog_bool_or_de_morgan, lhsOrDeMorgan, rhsOrDeMorgan,
      singletonOr, tailOr, mkNot, eoNot] at hX hY hZs ⊢

private theorem typeof_eq_not_left_bool {A B : Term} :
    __eo_typeof_eq (__eo_typeof (eoNot A)) (__eo_typeof B) = Term.Bool ->
    __eo_typeof A = Term.Bool ∧ __eo_typeof B = Term.Bool := by
  intro hTy
  change __eo_typeof_eq (__eo_typeof_not (__eo_typeof A)) (__eo_typeof B) =
    Term.Bool at hTy
  cases hA : __eo_typeof A <;> cases hB : __eo_typeof B <;>
    simp [__eo_typeof_eq, __eo_typeof_not, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not, hA, hB] at hTy ⊢

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

private theorem bool_or_de_morgan_data (x y zs : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation zs ->
    __eo_typeof (__eo_prog_bool_or_de_morgan x y zs) = Term.Bool ->
    RuleProofs.eo_has_bool_type x ∧
      RuleProofs.eo_has_bool_type y ∧
      RuleProofs.eo_has_bool_type zs ∧
      CnfSupport.OrList (tailOr y zs) ∧
      RuleProofs.eo_has_bool_type (singletonOr y zs) := by
  intro hXTrans hYTrans hZsTrans hResultTy
  have hXNe : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hYNe : y ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hZsNe : zs ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation zs hZsTrans
  have hProgEq := prog_bool_or_de_morgan_eq_of_ne_stuck x y zs hXNe hYNe hZsNe
  have hProgNe : __eo_prog_bool_or_de_morgan x y zs ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  rw [hProgEq] at hProgNe hResultTy
  have hRhsNe : rhsOrDeMorgan x y zs ≠ Term.Stuck :=
    CnfSupport.mk_apply_ne_stuck_right hProgNe
  have hResultTy' :
      __eo_typeof
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) (lhsOrDeMorgan x y zs))
          (rhsOrDeMorgan x y zs)) = Term.Bool := hResultTy
  rw [CnfSupport.mk_apply_eq_apply
    (f := Term.Apply (Term.UOp UserOp.eq) (lhsOrDeMorgan x y zs))
    (a := rhsOrDeMorgan x y zs) (by simp) hRhsNe] at hResultTy'
  change __eo_typeof_eq (__eo_typeof (lhsOrDeMorgan x y zs))
    (__eo_typeof (rhsOrDeMorgan x y zs)) = Term.Bool at hResultTy'
  rcases typeof_eq_not_left_bool (A := eoOr x (tailOr y zs))
      (B := rhsOrDeMorgan x y zs) hResultTy' with
    ⟨hLeftArgType, hRhsType⟩
  change __eo_typeof_or (__eo_typeof x) (__eo_typeof (tailOr y zs)) = Term.Bool
    at hLeftArgType
  have hXType : __eo_typeof x = Term.Bool :=
    CnfSupport.typeof_or_eq_bool_left hLeftArgType
  have hTailType : __eo_typeof (tailOr y zs) = Term.Bool :=
    CnfSupport.typeof_or_eq_bool_right hLeftArgType
  change __eo_typeof_or (__eo_typeof y) (__eo_typeof zs) = Term.Bool at hTailType
  have hYType : __eo_typeof y = Term.Bool :=
    CnfSupport.typeof_or_eq_bool_left hTailType
  have hZsType : __eo_typeof zs = Term.Bool :=
    CnfSupport.typeof_or_eq_bool_right hTailType
  have hInnerType :
      __eo_typeof
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.and) (mkNot (singletonOr y zs)))
          (Term.Boolean true)) = Term.Bool :=
    CnfSupport.typeof_mk_apply_and_right_bool hRhsType
  have hInnerNe :
      __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.and) (mkNot (singletonOr y zs)))
        (Term.Boolean true) ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hInnerType
  have hInnerFnNe :
      __eo_mk_apply (Term.UOp UserOp.and) (mkNot (singletonOr y zs)) ≠
        Term.Stuck :=
    CnfSupport.mk_apply_ne_stuck_left hInnerNe
  have hMkNotNe : mkNot (singletonOr y zs) ≠ Term.Stuck :=
    CnfSupport.mk_apply_ne_stuck_right hInnerFnNe
  have hInnerType' := hInnerType
  rw [CnfSupport.mk_apply_eq_apply (f := Term.UOp UserOp.and)
    (a := mkNot (singletonOr y zs)) (by simp) hMkNotNe] at hInnerType'
  have hNotSingletonType : __eo_typeof (mkNot (singletonOr y zs)) = Term.Bool :=
    CnfSupport.typeof_mk_apply_and_left_bool hInnerType'
  have hSingletonType : __eo_typeof (singletonOr y zs) = Term.Bool :=
    typeof_mk_not_arg_bool hNotSingletonType
  have hSingletonNe : singletonOr y zs ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hSingletonType
  have hTailList : CnfSupport.OrList (tailOr y zs) :=
    CnfSupport.orList_of_singleton_elim_ne_stuck hSingletonNe
  have hXBool : RuleProofs.eo_has_bool_type x :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x Term.Bool (__eo_to_smt x) rfl hXTrans hXType
  have hYBool : RuleProofs.eo_has_bool_type y :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      y Term.Bool (__eo_to_smt y) rfl hYTrans hYType
  have hZsBool : RuleProofs.eo_has_bool_type zs :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      zs Term.Bool (__eo_to_smt zs) rfl hZsTrans hZsType
  have hTailBool : RuleProofs.eo_has_bool_type (tailOr y zs) :=
    RuleProofs.eo_has_bool_type_or_of_bool_args y zs hYBool hZsBool
  have hSingletonBool : RuleProofs.eo_has_bool_type (singletonOr y zs) :=
    CnfSupport.orList_singleton_elim_preserves_bool_type hTailList hTailBool
  exact ⟨hXBool, hYBool, hZsBool, hTailList, hSingletonBool⟩

private theorem typed___eo_prog_bool_or_de_morgan_impl (x y zs : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation zs ->
    __eo_typeof (__eo_prog_bool_or_de_morgan x y zs) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__eo_prog_bool_or_de_morgan x y zs) := by
  intro hXTrans hYTrans hZsTrans hResultTy
  have hXNe : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hYNe : y ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hZsNe : zs ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation zs hZsTrans
  rcases bool_or_de_morgan_data x y zs hXTrans hYTrans hZsTrans hResultTy with
    ⟨hXBool, hYBool, hZsBool, hTailList, hSingletonBool⟩
  have hTailBool : RuleProofs.eo_has_bool_type (tailOr y zs) :=
    RuleProofs.eo_has_bool_type_or_of_bool_args y zs hYBool hZsBool
  have hOrBool : RuleProofs.eo_has_bool_type (eoOr x (tailOr y zs)) :=
    RuleProofs.eo_has_bool_type_or_of_bool_args x (tailOr y zs) hXBool hTailBool
  have hLeftBool : RuleProofs.eo_has_bool_type (lhsOrDeMorgan x y zs) :=
    RuleProofs.eo_has_bool_type_not_of_bool_arg (eoOr x (tailOr y zs)) hOrBool
  have hNotXBool : RuleProofs.eo_has_bool_type (eoNot x) :=
    RuleProofs.eo_has_bool_type_not_of_bool_arg x hXBool
  have hNotSingletonBool : RuleProofs.eo_has_bool_type (mkNot (singletonOr y zs)) :=
    eo_has_bool_type_mk_not (singletonOr y zs) hSingletonBool
  have hInnerBool :
      RuleProofs.eo_has_bool_type
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.and) (mkNot (singletonOr y zs)))
          (Term.Boolean true)) :=
    eo_has_bool_type_mk_and_chain (mkNot (singletonOr y zs)) (Term.Boolean true)
      hNotSingletonBool RuleProofs.eo_has_bool_type_true
  have hRhsBool : RuleProofs.eo_has_bool_type (rhsOrDeMorgan x y zs) :=
    eo_has_bool_type_mk_and (eoNot x)
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.and) (mkNot (singletonOr y zs)))
        (Term.Boolean true))
      hNotXBool hInnerBool
  have hProgEq := prog_bool_or_de_morgan_eq_of_ne_stuck x y zs hXNe hYNe hZsNe
  rw [hProgEq]
  have hRhsNe : rhsOrDeMorgan x y zs ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type _ hRhsBool
  rw [CnfSupport.mk_apply_eq_apply
    (f := Term.Apply (Term.UOp UserOp.eq) (lhsOrDeMorgan x y zs))
    (a := rhsOrDeMorgan x y zs) (by simp) hRhsNe]
  exact CnfSupport.eo_has_bool_type_eq_of_bool_args
    (lhsOrDeMorgan x y zs) (rhsOrDeMorgan x y zs) hLeftBool hRhsBool

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

private theorem facts___eo_prog_bool_or_de_morgan_impl
    (M : SmtModel) (hM : model_wf M) (x y zs : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation zs ->
    __eo_typeof (__eo_prog_bool_or_de_morgan x y zs) = Term.Bool ->
    eo_interprets M (__eo_prog_bool_or_de_morgan x y zs) true := by
  intro hXTrans hYTrans hZsTrans hResultTy
  have hXNe : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hYNe : y ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hZsNe : zs ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation zs hZsTrans
  rcases bool_or_de_morgan_data x y zs hXTrans hYTrans hZsTrans hResultTy with
    ⟨hXBool, hYBool, hZsBool, hTailList, hSingletonBool⟩
  have hTailBool : RuleProofs.eo_has_bool_type (tailOr y zs) :=
    RuleProofs.eo_has_bool_type_or_of_bool_args y zs hYBool hZsBool
  have hOrBool : RuleProofs.eo_has_bool_type (eoOr x (tailOr y zs)) :=
    RuleProofs.eo_has_bool_type_or_of_bool_args x (tailOr y zs) hXBool hTailBool
  have hLeftBool : RuleProofs.eo_has_bool_type (lhsOrDeMorgan x y zs) :=
    RuleProofs.eo_has_bool_type_not_of_bool_arg (eoOr x (tailOr y zs)) hOrBool
  have hProgBool :
      RuleProofs.eo_has_bool_type (__eo_prog_bool_or_de_morgan x y zs) :=
    typed___eo_prog_bool_or_de_morgan_impl x y zs hXTrans hYTrans hZsTrans hResultTy
  have hProgEq := prog_bool_or_de_morgan_eq_of_ne_stuck x y zs hXNe hYNe hZsNe
  rw [hProgEq]
  have hNotXBool : RuleProofs.eo_has_bool_type (eoNot x) :=
    RuleProofs.eo_has_bool_type_not_of_bool_arg x hXBool
  have hNotSingletonBool : RuleProofs.eo_has_bool_type (mkNot (singletonOr y zs)) :=
    eo_has_bool_type_mk_not (singletonOr y zs) hSingletonBool
  have hInnerBool :
      RuleProofs.eo_has_bool_type
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.and) (mkNot (singletonOr y zs)))
          (Term.Boolean true)) :=
    eo_has_bool_type_mk_and_chain (mkNot (singletonOr y zs)) (Term.Boolean true)
      hNotSingletonBool RuleProofs.eo_has_bool_type_true
  have hRhsBool : RuleProofs.eo_has_bool_type (rhsOrDeMorgan x y zs) :=
    eo_has_bool_type_mk_and (eoNot x)
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.and) (mkNot (singletonOr y zs)))
        (Term.Boolean true))
      hNotXBool hInnerBool
  have hRhsNe : rhsOrDeMorgan x y zs ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type _ hRhsBool
  rw [CnfSupport.mk_apply_eq_apply
    (f := Term.Apply (Term.UOp UserOp.eq) (lhsOrDeMorgan x y zs))
    (a := rhsOrDeMorgan x y zs) (by simp) hRhsNe]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [hProgEq, CnfSupport.mk_apply_eq_apply
      (f := Term.Apply (Term.UOp UserOp.eq) (lhsOrDeMorgan x y zs))
      (a := rhsOrDeMorgan x y zs) (by simp) hRhsNe] using hProgBool
  · rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM x hXBool with
      ⟨bx, hEvalX⟩
    rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM
        (tailOr y zs) hTailBool with
      ⟨bt, hEvalTail⟩
    have hSingletonEval :
        __smtx_model_eval M (__eo_to_smt (singletonOr y zs)) =
          __smtx_model_eval M (__eo_to_smt (tailOr y zs)) :=
      bool_eval_eq_of_true_iff M hM (singletonOr y zs) (tailOr y zs)
        hSingletonBool hTailBool
        (CnfSupport.orList_singleton_elim_true_iff M hM hTailList hTailBool)
    have hSingletonNe : singletonOr y zs ≠ Term.Stuck :=
      RuleProofs.term_ne_stuck_of_has_bool_type _ hSingletonBool
    have hMkNotEq : mkNot (singletonOr y zs) = eoNot (singletonOr y zs) :=
      CnfSupport.mk_apply_eq_apply (f := Term.UOp UserOp.not)
        (a := singletonOr y zs) (by simp) hSingletonNe
    have hMkNotNe : mkNot (singletonOr y zs) ≠ Term.Stuck := by
      rw [hMkNotEq]
      simp [eoNot]
    have hInnerEq :
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.and) (mkNot (singletonOr y zs)))
          (Term.Boolean true) =
          eoAnd (eoNot (singletonOr y zs)) (Term.Boolean true) := by
      rw [CnfSupport.mk_apply_eq_apply (f := Term.UOp UserOp.and)
        (a := mkNot (singletonOr y zs)) (by simp) hMkNotNe]
      rw [hMkNotEq]
      rw [CnfSupport.mk_apply_eq_apply
        (f := Term.Apply (Term.UOp UserOp.and) (eoNot (singletonOr y zs)))
        (a := Term.Boolean true) (by simp [eoNot]) (by simp)]
    have hRhsEq :
        rhsOrDeMorgan x y zs =
          eoAnd (eoNot x)
            (eoAnd (eoNot (singletonOr y zs)) (Term.Boolean true)) := by
      unfold rhsOrDeMorgan
      rw [hInnerEq]
      rw [CnfSupport.mk_apply_eq_apply
        (f := Term.Apply (Term.UOp UserOp.and) (eoNot x))
        (a := eoAnd (eoNot (singletonOr y zs)) (Term.Boolean true))
        (by simp [eoNot]) (by simp [eoAnd, eoNot])]
    rw [show __eo_to_smt (lhsOrDeMorgan x y zs) =
      SmtTerm.not (SmtTerm.or (__eo_to_smt x) (__eo_to_smt (tailOr y zs))) by
      rfl]
    rw [show __eo_to_smt (rhsOrDeMorgan x y zs) =
      SmtTerm.and (SmtTerm.not (__eo_to_smt x))
        (SmtTerm.and (SmtTerm.not (__eo_to_smt (singletonOr y zs)))
          (SmtTerm.Boolean true)) by
      rw [hRhsEq]
      rfl]
    rw [__smtx_model_eval.eq_7, __smtx_model_eval.eq_8, __smtx_model_eval.eq_9,
      __smtx_model_eval.eq_7, __smtx_model_eval.eq_9, __smtx_model_eval.eq_7,
      __smtx_model_eval.eq_1, hEvalX, hEvalTail, hSingletonEval, hEvalTail]
    cases bx <;> cases bt <;>
      simp [RuleProofs.smt_value_rel, __smtx_model_eval_eq, __smtx_model_eval_and,
        __smtx_model_eval_or, __smtx_model_eval_not, native_veq, SmtEval.native_and,
        SmtEval.native_or, SmtEval.native_not]

public theorem cmd_step_bool_or_de_morgan_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_or_de_morgan args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bool_or_de_morgan args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_or_de_morgan args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bool_or_de_morgan args premises ≠ Term.Stuck :=
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
                      change __eo_typeof (__eo_prog_bool_or_de_morgan a1 a2 a3) =
                        Term.Bool at hResultTy
                      refine ⟨?_, ?_⟩
                      · intro _hTrue
                        change eo_interprets M (__eo_prog_bool_or_de_morgan a1 a2 a3) true
                        exact facts___eo_prog_bool_or_de_morgan_impl M hM a1 a2 a3
                          hATrans.1 hATrans.2.1 hATrans.2.2.1 hResultTy
                      · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                          (typed___eo_prog_bool_or_de_morgan_impl a1 a2 a3
                            hATrans.1 hATrans.2.1 hATrans.2.2.1 hResultTy)
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
