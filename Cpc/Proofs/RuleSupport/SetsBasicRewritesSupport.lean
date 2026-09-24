module

public import Cpc.Proofs.RuleSupport.SetsEvalOpSupport
import all Cpc.Proofs.RuleSupport.SetsEvalOpSupport
public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport

public section

open Eo
open SmtEval
open Smtm
open SetsEvalOpSupport
open SetsMemberSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

namespace SetsBasicRewritesSupport

def mkEq (a b : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b

def mkSetEmpty (T : Term) : Term :=
  Term.UOp1 UserOp1.set_empty (Term.Apply (Term.UOp UserOp.Set) T)

def mkSetSingleton (x : Term) : Term :=
  Term.Apply (Term.UOp UserOp.set_singleton) x

def mkSetUnion (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.set_union) x) y

def mkSetInter (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.set_inter) x) y

def mkSetMinus (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.set_minus) x) y

def mkSetMember (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.set_member) x) y

theorem eo_to_smt_type_set_of_non_none
    (T : Term)
    (h : __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T) ≠ SmtType.None) :
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T) =
      SmtType.Set (__eo_to_smt_type T) := by
  cases hT : __eo_to_smt_type T <;>
    simp [TranslationProofs.eo_to_smt_type_set, __smtx_typeof_guard,
      native_ite, native_Teq, hT] at h ⊢

theorem eo_to_smt_type_set_component_non_none
    (T : Term)
    (h : __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T) ≠ SmtType.None) :
    __eo_to_smt_type T ≠ SmtType.None := by
  cases hT : __eo_to_smt_type T <;>
    simp [TranslationProofs.eo_to_smt_type_set, __smtx_typeof_guard,
      native_ite, native_Teq, hT] at h ⊢

theorem eo_typeof_set_union_ne_stuck_info
    {A B : Term}
    (h : __eo_typeof_set_union A B ≠ Term.Stuck) :
    ∃ T : Term,
      A = Term.Apply (Term.UOp UserOp.Set) T ∧
        B = Term.Apply (Term.UOp UserOp.Set) T ∧
          __eo_typeof_set_union A B =
            Term.Apply (Term.UOp UserOp.Set) T := by
  cases A <;> try simp [__eo_typeof_set_union] at h
  next f T =>
    cases f <;> try simp [__eo_typeof_set_union] at h
    next op =>
      cases op <;> try simp [__eo_typeof_set_union] at h
      cases B <;> try simp [__eo_typeof_set_union] at h
      next g U =>
        cases g <;> try simp [__eo_typeof_set_union] at h
        next opB =>
          cases opB <;> try simp [__eo_typeof_set_union] at h
          have hEq : U = T :=
            RuleProofs.eq_of_requires_eq_true_not_stuck T U
              (Term.Apply (Term.UOp UserOp.Set) T) h
          subst U
          have hRes :
              __eo_requires (__eo_eq T T) (Term.Boolean true)
                  (Term.Apply (Term.UOp UserOp.Set) T) =
                Term.Apply (Term.UOp UserOp.Set) T :=
            req_result h
          exact ⟨T, rfl, rfl, by
            simpa [__eo_typeof_set_union] using hRes⟩

theorem eo_typeof_set_union_bool_info
    {x y rhs : Term}
    (hTy : __eo_typeof (mkEq (mkSetUnion x y) rhs) = Term.Bool) :
    ∃ T : Term,
      __eo_typeof x = Term.Apply (Term.UOp UserOp.Set) T ∧
        __eo_typeof y = Term.Apply (Term.UOp UserOp.Set) T ∧
          __eo_typeof rhs = Term.Apply (Term.UOp UserOp.Set) T := by
  have hEqTy :
      __eo_typeof_eq
        (__eo_typeof_set_union (__eo_typeof x) (__eo_typeof y))
        (__eo_typeof rhs) = Term.Bool := by
    have hsimpa := hTy
    try simp [mkEq, mkSetUnion] at hsimpa ⊢
    exact hsimpa
  rcases SetsMemberSupport.eo_typeof_eq_eq_bool_info hEqTy with
    ⟨hSame, hUnionNS⟩
  rcases eo_typeof_set_union_ne_stuck_info hUnionNS with
    ⟨T, hxTy, hyTy, hUnionTy⟩
  exact ⟨T, hxTy, hyTy, by rw [← hSame, hUnionTy]⟩

theorem eo_typeof_set_subset_ne_stuck_info
    {A B : Term}
    (h : __eo_typeof_set_subset A B ≠ Term.Stuck) :
    ∃ T : Term,
      A = Term.Apply (Term.UOp UserOp.Set) T ∧
        B = Term.Apply (Term.UOp UserOp.Set) T ∧
          T ≠ Term.Stuck := by
  cases A <;> try simp [__eo_typeof_set_subset] at h
  next f T =>
    cases f <;> try simp [__eo_typeof_set_subset] at h
    next op =>
      cases op <;> try simp [__eo_typeof_set_subset] at h
      cases B <;> try simp [__eo_typeof_set_subset] at h
      next g U =>
        cases g <;> try simp [__eo_typeof_set_subset] at h
        next opB =>
          cases opB <;> try simp [__eo_typeof_set_subset] at h
          have hEq : U = T :=
            RuleProofs.eq_of_requires_eq_true_not_stuck T U Term.Bool h
          subst U
          refine ⟨T, rfl, rfl, ?_⟩
          intro hStuck
          subst hStuck
          simp [__eo_requires, __eo_eq, native_ite, native_teq] at h

/-- Extracts the operand set types from a `(= (set_subset x y) rhs)` formula
    whose `__eo_typeof` is `Bool`. -/
theorem eo_typeof_set_subset_eq_bool_info
    {x y rhs : Term}
    (hTy :
      __eo_typeof
        (mkEq
          (Term.Apply (Term.Apply Term.set_subset x) y)
          rhs) = Term.Bool) :
    ∃ T : Term,
      __eo_typeof x = Term.Apply (Term.UOp UserOp.Set) T ∧
        __eo_typeof y = Term.Apply (Term.UOp UserOp.Set) T ∧
          __eo_typeof rhs = Term.Bool ∧
          T ≠ Term.Stuck := by
  have hEqTy :
      __eo_typeof_eq
        (__eo_typeof_set_subset (__eo_typeof x) (__eo_typeof y))
        (__eo_typeof rhs) = Term.Bool := by
    have hsimpa := hTy
    try simp [mkEq] at hsimpa ⊢
    exact hsimpa
  rcases SetsMemberSupport.eo_typeof_eq_eq_bool_info hEqTy with
    ⟨hSame, hSubsetNS⟩
  rcases eo_typeof_set_subset_ne_stuck_info hSubsetNS with
    ⟨T, hxTy, hyTy, hTNS⟩
  refine ⟨T, hxTy, hyTy, ?_, hTNS⟩
  -- subset type is Bool, and rhs type equals subset type
  have hSubsetReq :
      __eo_typeof_set_subset (__eo_typeof x) (__eo_typeof y) =
        __eo_requires (__eo_eq T T) (Term.Boolean true) Term.Bool := by
    rw [hxTy, hyTy]
    rfl
  have hSubsetBool :
      __eo_typeof_set_subset (__eo_typeof x) (__eo_typeof y) = Term.Bool := by
    rw [hSubsetReq]
    exact req_result (by rw [← hSubsetReq]; exact hSubsetNS)
  rw [← hSame, hSubsetBool]

private theorem set_smt_types_of_eo_set_types
    {x y : Term} {T : Term}
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hyTrans : RuleProofs.eo_has_smt_translation y)
    (hxTy : __eo_typeof x = Term.Apply (Term.UOp UserOp.Set) T)
    (hyTy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Set) T) :
    let A := __eo_to_smt_type T
    __smtx_typeof (__eo_to_smt x) = SmtType.Set A ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.Set A ∧
        A ≠ SmtType.None := by
  intro A
  have hxMatch :
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hxTrans
  have hyMatch :
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation y hyTrans
  have hSetNonNone :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T) ≠ SmtType.None := by
    have hRaw : __eo_to_smt_type (__eo_typeof x) ≠ SmtType.None := by
      rw [← hxMatch]
      exact hxTrans
    simpa [hxTy] using hRaw
  have hSetTy :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T) =
        SmtType.Set (__eo_to_smt_type T) :=
    eo_to_smt_type_set_of_non_none T hSetNonNone
  have hTNonNone : __eo_to_smt_type T ≠ SmtType.None :=
    eo_to_smt_type_set_component_non_none T hSetNonNone
  exact ⟨by simpa [A, hxTy, hSetTy] using hxMatch,
    by simpa [A, hyTy, hSetTy] using hyMatch, by simpa [A] using hTNonNone⟩

theorem typed_set_union_eq_right
    (x y rhs : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hyTrans : RuleProofs.eo_has_smt_translation y)
    (hrhsTrans : RuleProofs.eo_has_smt_translation rhs)
    (hTy : __eo_typeof (mkEq (mkSetUnion x y) rhs) = Term.Bool) :
    RuleProofs.eo_has_bool_type (mkEq (mkSetUnion x y) rhs) := by
  rcases eo_typeof_set_union_bool_info (x := x) (y := y) (rhs := rhs) hTy with
    ⟨T, hxTy, hyTy, hrhsTy⟩
  rcases set_smt_types_of_eo_set_types hxTrans hyTrans hxTy hyTy with
    ⟨hxSmtTy, hySmtTy, hTNonNone⟩
  rcases set_smt_types_of_eo_set_types hxTrans hrhsTrans hxTy hrhsTy with
    ⟨_hxSmtTy', hrhsSmtTy, _⟩
  have hSetWf : __smtx_type_wf (SmtType.Set (__eo_to_smt_type T)) = true :=
    Smtm.smt_term_set_type_wf_of_non_none
      (__eo_to_smt y)
      (by
        unfold term_has_non_none_type
        rw [hySmtTy]
        simp)
      hySmtTy
  unfold RuleProofs.eo_has_bool_type
  change
    __smtx_typeof
        (SmtTerm.eq (SmtTerm.set_union (__eo_to_smt x) (__eo_to_smt y))
          (__eo_to_smt rhs)) = SmtType.Bool
  rw [typeof_eq_eq, typeof_set_union_eq]
  simp [__smtx_typeof_sets_op_2, __smtx_typeof_eq, native_ite, native_Teq,
    __smtx_typeof_guard, hxSmtTy, hySmtTy, hrhsSmtTy, hSetWf]

theorem set_empty_smt_type
    (T : Term)
    (hTNonNone : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T) =
      SmtType.Set (__eo_to_smt_type T) :=
  eo_to_smt_type_set_of_non_none T (by
    simpa [TranslationProofs.eo_to_smt_type_set,
      TranslationProofs.smtx_typeof_guard_of_non_none
        (__eo_to_smt_type T) (SmtType.Set (__eo_to_smt_type T)) hTNonNone])

theorem model_eval_set_empty
    (M : SmtModel) (T : Term)
    (hTNonNone : __eo_to_smt_type T ≠ SmtType.None) :
    __smtx_model_eval M (__eo_to_smt (mkSetEmpty T)) =
      SmtValue.Set
        (SmtMap.default (__eo_to_smt_type T) (SmtValue.Boolean false)) := by
  have hSetTy := set_empty_smt_type T hTNonNone
  change
    __smtx_model_eval M
        (__eo_to_smt_set_empty
          (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T))) = _
  rw [hSetTy]
  simp [__eo_to_smt_set_empty, __smtx_model_eval]

theorem set_empty_map_canonical' (A : SmtType) :
    __smtx_map_canonical
        (SmtMap.default A (SmtValue.Boolean false)) = true :=
  set_empty_map_canonical A

theorem set_empty_map_type (A : SmtType) :
    __smtx_typeof_map_value
        (SmtMap.default A (SmtValue.Boolean false)) =
      SmtType.Map A SmtType.Bool := by
  simp [__smtx_typeof_map_value, __smtx_typeof_value]

theorem set_empty_map_default_leaf (A : SmtType) :
    smt_map_default_leaf (SmtMap.default A (SmtValue.Boolean false)) =
      SmtMap.default A (SmtValue.Boolean false) := by
  rfl

theorem set_map_lookup_eq_default_of_not_typed_canonical :
    ∀ {m : SmtMap} {A B : SmtType} {v : SmtValue},
      __smtx_typeof_map_value m = SmtType.Map A B ->
        __smtx_map_canonical m = true ->
          ¬ (__smtx_typeof_value v = A ∧
              __smtx_value_canonical v = true) ->
            __smtx_map_lookup m v = __smtx_map_get_default m
  | SmtMap.default T e, A, B, v, _hTy, _hCan, _hNot => by
      simp [__smtx_map_lookup, __smtx_map_get_default]
  | SmtMap.cons i e m, A, B, v, hTy, hCan, hNot => by
      have hmTy : __smtx_typeof_map_value m = SmtType.Map A B := by
        by_cases hEqTy :
            native_Teq
              (SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e))
              (__smtx_typeof_map_value m)
        · simpa [__smtx_typeof_map_value, native_ite, hEqTy] using hTy
        · simp [__smtx_typeof_map_value, native_ite, hEqTy] at hTy
      have hEqTy' :
          SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e) =
            __smtx_typeof_map_value m := by
        by_cases hEqTy :
            native_Teq
              (SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e))
              (__smtx_typeof_map_value m)
        · simpa [native_Teq] using hEqTy
        · simp [__smtx_typeof_map_value, native_ite, hEqTy] at hTy
      have hHead :
          SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e) =
            SmtType.Map A B := hEqTy'.trans hmTy
      have hiTy : __smtx_typeof_value i = A := by
        cases hHead
        rfl
      have hiCan : __smtx_value_canonical i = true := by
        have hParts := hCan
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        exact hParts.1.1.1.1
      have hmCan : __smtx_map_canonical m = true := by
        have hParts := hCan
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        exact hParts.1.1.2
      by_cases hivTrue : native_veq i v = true
      · have hiv : i = v := Smtm.eq_of_native_veq_true hivTrue
        subst v
        exact False.elim (hNot ⟨hiTy, hiCan⟩)
      · have hivFalse : native_veq i v = false := by
          cases hBool : native_veq i v <;> simp [hBool] at hivTrue ⊢
        have hRec :=
          set_map_lookup_eq_default_of_not_typed_canonical hmTy hmCan hNot
        simpa [__smtx_map_lookup, __smtx_map_get_default, native_ite,
          hivFalse] using hRec

theorem set_map_lookup_bool_ite_true_false
    {m : SmtMap} {A : SmtType} (v : SmtValue)
    (hmTy : __smtx_typeof_map_value m = SmtType.Map A SmtType.Bool)
    (hmCan : __smtx_map_canonical m = true)
    (hmDef : __smtx_map_get_default m = SmtValue.Boolean false) :
    native_ite
        (native_veq (__smtx_map_lookup m v) (SmtValue.Boolean true))
        (SmtValue.Boolean true) (SmtValue.Boolean false) =
      __smtx_map_lookup m v := by
  by_cases hv :
      __smtx_typeof_value v = A ∧ __smtx_value_canonical v = true
  · have hLookupTy :
        __smtx_typeof_value (__smtx_map_lookup m v) = SmtType.Bool :=
      Smtm.map_lookup_typed hmTy hv.1
    rcases bool_value_canonical hLookupTy with ⟨b, hLookup⟩
    rw [hLookup]
    cases b <;> simp [native_ite, native_veq]
  · have hLookupDefault :
        __smtx_map_lookup m v = __smtx_map_get_default m :=
      set_map_lookup_eq_default_of_not_typed_canonical hmTy hmCan hv
    rw [hLookupDefault, hmDef]
    simp [native_ite, native_veq]

theorem set_eval_eq_empty_of_premise
    (M : SmtModel) (hM : model_wf M) (x T : Term)
    (hXTy : __smtx_typeof (__eo_to_smt x) = SmtType.Set (__eo_to_smt_type T))
    (hTNonNone : __eo_to_smt_type T ≠ SmtType.None)
    (hPrem :
      eo_interprets M (mkEq x (mkSetEmpty T)) true) :
    __smtx_model_eval M (__eo_to_smt x) =
      SmtValue.Set
        (SmtMap.default (__eo_to_smt_type T) (SmtValue.Boolean false)) := by
  have hRel := RuleProofs.eo_interprets_eq_rel M x (mkSetEmpty T) hPrem
  have hEmptyEval := model_eval_set_empty M T hTNonNone
  have hEmptyTy :
      __smtx_typeof_value
          (SmtValue.Set
            (SmtMap.default (__eo_to_smt_type T) (SmtValue.Boolean false))) =
        SmtType.Set (__eo_to_smt_type T) := by
    simp [__smtx_typeof_value, __smtx_map_to_set_type, set_empty_map_type]
  have hXEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.Set (__eo_to_smt_type T) := by
    simpa [hXTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x)
        (by
          unfold term_has_non_none_type
          rw [hXTy]
          simp)
  have hEq :=
    RuleProofs.smt_value_rel_eq_of_type_ne_reglan
      (v1 := __smtx_model_eval M (__eo_to_smt x))
      (v2 := SmtValue.Set
        (SmtMap.default (__eo_to_smt_type T) (SmtValue.Boolean false)))
      hXEvalTy hEmptyTy (by intro h; cases h)
      (by simpa [hEmptyEval] using hRel)
  exact hEq

theorem set_union_empty_left_rel
    (M : SmtModel) (hM : model_wf M)
    (x y T : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hyTrans : RuleProofs.eo_has_smt_translation y)
    (hXTy : __eo_typeof x = Term.Apply (Term.UOp UserOp.Set) T)
    (hYTy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Set) T)
    (hPrem : eo_interprets M (mkEq x (mkSetEmpty T)) true) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkSetUnion x y)))
      (__smtx_model_eval M (__eo_to_smt y)) := by
  rcases set_smt_types_of_eo_set_types hxTrans hyTrans hXTy hYTy with
    ⟨hXSmtTy, hYSmtTy, hTNonNone⟩
  have hXEval := set_eval_eq_empty_of_premise M hM x T hXSmtTy hTNonNone hPrem
  rcases set_value_facts M hM y (__eo_to_smt_type T) hyTrans hYSmtTy with
    ⟨my, hYEval, _hYCan, _hYTy, _hYDef⟩
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M
      (SmtTerm.set_union (__eo_to_smt x) (__eo_to_smt y)))
    (__smtx_model_eval M (__eo_to_smt y))
  rw [model_eval_union_eq M (__eo_to_smt x) (__eo_to_smt y), hXEval, hYEval]
  change RuleProofs.smt_value_rel
    (__smtx_set_union
      (SmtValue.Set
        (SmtMap.default (__eo_to_smt_type T) (SmtValue.Boolean false)))
      (SmtValue.Set my))
    (SmtValue.Set my)
  simp [__smtx_set_union, __smtx_set_op_rec]
  exact RuleProofs.smt_value_rel_refl (SmtValue.Set my)

theorem eo_typeof_set_empty_set_eq
    {T U : Term}
    (h :
      __eo_typeof (mkSetEmpty T) =
        Term.Apply (Term.UOp UserOp.Set) U) :
    U = T := by
  unfold mkSetEmpty at h
  change
    __eo_typeof_set_empty
        (__eo_typeof (Term.Apply (Term.UOp UserOp.Set) T))
        (Term.Apply (Term.UOp UserOp.Set) T) =
      Term.Apply (Term.UOp UserOp.Set) U at h
  change
    __eo_typeof_set_empty (__eo_typeof_Seq (__eo_typeof T))
        (Term.Apply (Term.UOp UserOp.Set) T) =
      Term.Apply (Term.UOp UserOp.Set) U at h
  cases hTy : __eo_typeof T <;>
    simp [__eo_typeof_Seq, __eo_typeof_set_empty,
      __eo_disamb_type_set_empty, hTy] at h
  exact h.symm

theorem eo_typeof_set_minus_self_bool_info
    {x T : Term}
    (hTy : __eo_typeof (mkEq (mkSetMinus x x) (mkSetEmpty T)) = Term.Bool) :
    __eo_typeof x = Term.Apply (Term.UOp UserOp.Set) T := by
  have hEqTy :
      __eo_typeof_eq
          (__eo_typeof_set_union (__eo_typeof x) (__eo_typeof x))
          (__eo_typeof (mkSetEmpty T)) = Term.Bool := by
    have hsimpa := hTy
    try simp [mkEq, mkSetMinus] at hsimpa ⊢
    exact hsimpa
  rcases SetsMemberSupport.eo_typeof_eq_eq_bool_info hEqTy with
    ⟨hSame, hMinusNS⟩
  rcases eo_typeof_set_union_ne_stuck_info hMinusNS with
    ⟨U, hxTy, _hxTy', hMinusTy⟩
  have hEmptyTy :
      __eo_typeof (mkSetEmpty T) =
        Term.Apply (Term.UOp UserOp.Set) U := by
    rw [← hSame, hMinusTy]
  have hU : U = T := eo_typeof_set_empty_set_eq hEmptyTy
  simpa [hU] using hxTy

theorem smt_typeof_mkSetEmpty_of_set_type_wf
    (T : Term)
    (hTypeWf :
      __smtx_type_wf
        (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T)) = true) :
    __smtx_typeof (__eo_to_smt (mkSetEmpty T)) =
      SmtType.Set (__eo_to_smt_type T) := by
  have hSetNonNone :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T) ≠
        SmtType.None :=
    Smtm.type_wf_non_none hTypeWf
  have hSetTy :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T) =
        SmtType.Set (__eo_to_smt_type T) :=
    eo_to_smt_type_set_of_non_none T hSetNonNone
  have hSetWf :
      __smtx_type_wf (SmtType.Set (__eo_to_smt_type T)) = true := by
    simpa [hSetTy] using hTypeWf
  change
    __smtx_typeof
        (__eo_to_smt_set_empty
          (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T))) =
      SmtType.Set (__eo_to_smt_type T)
  rw [hSetTy]
  simp [__eo_to_smt_set_empty, smtx_typeof_set_empty_term_eq,
    __smtx_typeof_guard_wf, hSetWf, native_ite]

theorem set_union_empty_left_rel_of_premise_bool
    (M : SmtModel) (hM : model_wf M)
    (x y T : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hyTrans : RuleProofs.eo_has_smt_translation y)
    (hTypeWf :
      __smtx_type_wf
        (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T)) = true)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq x (mkSetEmpty T)))
    (hFormulaTy : __eo_typeof (mkEq (mkSetUnion x y) y) = Term.Bool)
    (hPrem : eo_interprets M (mkEq x (mkSetEmpty T)) true) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkSetUnion x y)))
      (__smtx_model_eval M (__eo_to_smt y)) := by
  rcases eo_typeof_set_union_bool_info (x := x) (y := y) (rhs := y)
      hFormulaTy with
    ⟨U, hxTy, hyTy, _hyTy'⟩
  rcases set_smt_types_of_eo_set_types hxTrans hyTrans hxTy hyTy with
    ⟨hXSmtTyU, hYSmtTyU, _hUNonNone⟩
  have hEmptyTy :
      __smtx_typeof (__eo_to_smt (mkSetEmpty T)) =
        SmtType.Set (__eo_to_smt_type T) :=
    smt_typeof_mkSetEmpty_of_set_type_wf T hTypeWf
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      x (mkSetEmpty T) hPremBool with
    ⟨hXEmptyTy, _hXNonNone⟩
  have hXSmtTyT :
      __smtx_typeof (__eo_to_smt x) = SmtType.Set (__eo_to_smt_type T) :=
    hXEmptyTy.trans hEmptyTy
  have hElemTy : __eo_to_smt_type U = __eo_to_smt_type T := by
    rw [hXSmtTyT] at hXSmtTyU
    injection hXSmtTyU with hEq
    exact hEq.symm
  have hYSmtTyT :
      __smtx_typeof (__eo_to_smt y) = SmtType.Set (__eo_to_smt_type T) := by
    simpa [hElemTy] using hYSmtTyU
  have hSetNonNone :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T) ≠
        SmtType.None :=
    Smtm.type_wf_non_none hTypeWf
  have hTNonNone : __eo_to_smt_type T ≠ SmtType.None :=
    eo_to_smt_type_set_component_non_none T hSetNonNone
  have hXEval := set_eval_eq_empty_of_premise M hM x T hXSmtTyT
    hTNonNone hPrem
  rcases set_value_facts M hM y (__eo_to_smt_type T) hyTrans hYSmtTyT with
    ⟨my, hYEval, _hYCan, _hYTy, _hYDef⟩
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M
      (SmtTerm.set_union (__eo_to_smt x) (__eo_to_smt y)))
    (__smtx_model_eval M (__eo_to_smt y))
  rw [model_eval_union_eq M (__eo_to_smt x) (__eo_to_smt y), hXEval, hYEval]
  change RuleProofs.smt_value_rel
    (__smtx_set_union
      (SmtValue.Set
        (SmtMap.default (__eo_to_smt_type T) (SmtValue.Boolean false)))
      (SmtValue.Set my))
    (SmtValue.Set my)
  simp [__smtx_set_union, __smtx_set_op_rec]
  exact RuleProofs.smt_value_rel_refl (SmtValue.Set my)

theorem prog_sets_union_emp1_info
    (x y ty P : Term)
    (hProg :
      __eo_prog_sets_union_emp1 x y ty (Proof.pf P) ≠ Term.Stuck) :
    ∃ T x0 T0 : Term,
      ty = Term.Apply (Term.UOp UserOp.Set) T ∧
        P = mkEq x0 (mkSetEmpty T0) ∧
          x0 = x ∧
            T0 = T ∧
              __eo_prog_sets_union_emp1 x y ty (Proof.pf P) =
                mkEq (mkSetUnion x y) y := by
  by_cases hx : x = Term.Stuck
  · subst x
    simp [__eo_prog_sets_union_emp1] at hProg
  by_cases hy : y = Term.Stuck
  · subst y
    simp [__eo_prog_sets_union_emp1, hx] at hProg
  cases ty with
  | Apply f T =>
      cases f with
      | UOp op =>
          by_cases hSet : op = UserOp.Set
          · subst op
            cases P with
            | Apply pf rhs =>
                cases pf with
                | Apply pg x0 =>
                    cases pg with
                    | UOp eqOp =>
                        by_cases hEq : eqOp = UserOp.eq
                        · subst eqOp
                          cases rhs with
                          | UOp1 emptyOp setTy =>
                              by_cases hEmpty : emptyOp = UserOp1.set_empty
                              · subst emptyOp
                                cases setTy with
                                | Apply setF T0 =>
                                    cases setF with
                                    | UOp setOp =>
                                        by_cases hSetTy : setOp = UserOp.Set
                                        · subst setOp
                                          let B := mkEq (mkSetUnion x y) y
                                          have hReq :
                                              __eo_requires
                                                  (__eo_and (__eo_eq x x0)
                                                    (__eo_eq T T0))
                                                  (Term.Boolean true) B ≠
                                                Term.Stuck := by
                                            simpa [B, __eo_prog_sets_union_emp1,
                                              hx, hy, mkEq, mkSetUnion,
                                              mkSetEmpty] using hProg
                                          have hEqs :
                                              x0 = x ∧ T0 = T :=
                                            RuleProofs.eqs_of_requires_and_eq_true_not_stuck
                                              x T x0 T0 B hReq
                                          have hUnfold :
                                              __eo_prog_sets_union_emp1 x y
                                                  (Term.Apply
                                                    (Term.UOp UserOp.Set) T)
                                                  (Proof.pf
                                                    (mkEq x0 (mkSetEmpty T0))) =
                                                __eo_requires
                                                  (__eo_and (__eo_eq x x0)
                                                    (__eo_eq T T0))
                                                  (Term.Boolean true) B := by
                                            simp [B, __eo_prog_sets_union_emp1,
                                              hx, hy, mkEq, mkSetUnion,
                                              mkSetEmpty]
                                          refine ⟨T, x0, T0, rfl, rfl,
                                            hEqs.1, hEqs.2, ?_⟩
                                          change
                                            __eo_prog_sets_union_emp1 x y
                                                (Term.Apply
                                                  (Term.UOp UserOp.Set) T)
                                                (Proof.pf
                                                  (mkEq x0 (mkSetEmpty T0))) =
                                              mkEq (mkSetUnion x y) y
                                          rw [hUnfold, SetsEvalOpSupport.req_result hReq]
                                        · exfalso
                                          apply hProg
                                          simp [__eo_prog_sets_union_emp1, hx,
                                            hy, hSetTy, mkEq, mkSetEmpty]
                                    | _ =>
                                        exfalso
                                        apply hProg
                                        simp [__eo_prog_sets_union_emp1, hx,
                                          hy, mkEq, mkSetEmpty]
                                | _ =>
                                    exfalso
                                    apply hProg
                                    simp [__eo_prog_sets_union_emp1, hx, hy,
                                      mkEq, mkSetEmpty]
                              · exfalso
                                apply hProg
                                simp [__eo_prog_sets_union_emp1, hx, hy,
                                  hEmpty, mkEq, mkSetEmpty]
                          | _ =>
                              exfalso
                              apply hProg
                              simp [__eo_prog_sets_union_emp1, hx, hy, mkEq,
                                mkSetEmpty]
                        · exfalso
                          apply hProg
                          simp [__eo_prog_sets_union_emp1, hx, hy, hEq, mkEq,
                            mkSetEmpty]
                    | _ =>
                        exfalso
                        apply hProg
                        simp [__eo_prog_sets_union_emp1, hx, hy, mkEq,
                          mkSetEmpty]
                | _ =>
                    exfalso
                    apply hProg
                    simp [__eo_prog_sets_union_emp1, hx, hy, mkEq, mkSetEmpty]
            | _ =>
                exfalso
                apply hProg
                simp [__eo_prog_sets_union_emp1, hx, hy, mkEq, mkSetEmpty]
          · exfalso
            apply hProg
            simp [__eo_prog_sets_union_emp1, hx, hy, hSet]
      | _ =>
          exfalso
          apply hProg
          simp [__eo_prog_sets_union_emp1, hx, hy]
  | _ =>
      exfalso
      apply hProg
      simp [__eo_prog_sets_union_emp1, hx, hy]

theorem eo_typeof_set_member_false_bool_info
    {x y : Term}
    (hTy :
      __eo_typeof (mkEq (mkSetMember x y) (Term.Boolean false)) =
        Term.Bool) :
    ∃ T : Term,
      __eo_typeof x = T ∧
        __eo_typeof y = Term.Apply (Term.UOp UserOp.Set) T := by
  have hEqTy :
      __eo_typeof_eq
          (__eo_typeof_set_member (__eo_typeof x) (__eo_typeof y))
          Term.Bool = Term.Bool := by
    have hsimpa := hTy
    try simp [mkEq, mkSetMember] at hsimpa ⊢
    exact hsimpa
  rcases SetsMemberSupport.eo_typeof_eq_eq_bool_info hEqTy with
    ⟨hSame, _hMemberNS⟩
  have hMemberBool :
      __eo_typeof_set_member (__eo_typeof x) (__eo_typeof y) =
        Term.Bool := by
    simpa using hSame
  rcases SetsMemberSupport.eo_typeof_set_member_eq_bool_info hMemberBool with
    ⟨T, hxTy, hyTy, _hTNonStuck⟩
  exact ⟨T, hxTy, hyTy⟩

private theorem set_member_smt_types_of_eo_types
    {x y T : Term}
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hyTrans : RuleProofs.eo_has_smt_translation y)
    (hxTy : __eo_typeof x = T)
    (hyTy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Set) T) :
    let A := __eo_to_smt_type T
    __smtx_typeof (__eo_to_smt x) = A ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.Set A ∧
        A ≠ SmtType.None := by
  intro A
  have hxMatch :
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hxTrans
  have hyMatch :
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation y hyTrans
  have hSetNonNone :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T) ≠ SmtType.None := by
    have hRaw : __eo_to_smt_type (__eo_typeof y) ≠ SmtType.None := by
      rw [← hyMatch]
      exact hyTrans
    simpa [hyTy] using hRaw
  have hSetTy :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T) =
        SmtType.Set (__eo_to_smt_type T) :=
    eo_to_smt_type_set_of_non_none T hSetNonNone
  have hTNonNone : __eo_to_smt_type T ≠ SmtType.None :=
    eo_to_smt_type_set_component_non_none T hSetNonNone
  exact ⟨by simpa [A, hxTy] using hxMatch,
    by simpa [A, hyTy, hSetTy] using hyMatch, by simpa [A] using hTNonNone⟩

theorem typed_set_member_eq_false
    (x y : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hyTrans : RuleProofs.eo_has_smt_translation y)
    (hTy :
      __eo_typeof (mkEq (mkSetMember x y) (Term.Boolean false)) =
        Term.Bool) :
    RuleProofs.eo_has_bool_type
      (mkEq (mkSetMember x y) (Term.Boolean false)) := by
  rcases eo_typeof_set_member_false_bool_info hTy with
    ⟨T, hxTy, hyTy⟩
  rcases set_member_smt_types_of_eo_types hxTrans hyTrans hxTy hyTy with
    ⟨hxSmtTy, hySmtTy, hTNonNone⟩
  have hMemberTy :
      __smtx_typeof (__eo_to_smt (mkSetMember x y)) = SmtType.Bool := by
    change
      __smtx_typeof (SmtTerm.set_member (__eo_to_smt x) (__eo_to_smt y)) =
        SmtType.Bool
    rw [typeof_set_member_eq]
    simp [__smtx_typeof_set_member, hxSmtTy, hySmtTy, native_ite,
      native_Teq, hTNonNone]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (mkSetMember x y) (Term.Boolean false)
    (by rw [hMemberTy, RuleProofs.eo_to_smt_false_eq, __smtx_typeof.eq_1])
    (by rw [hMemberTy]; simp)

theorem set_member_empty_rel_of_premise_bool
    (M : SmtModel) (hM : model_wf M)
    (x y T : Term)
    (hyTrans : RuleProofs.eo_has_smt_translation y)
    (hTypeWf :
      __smtx_type_wf
        (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T)) = true)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq y (mkSetEmpty T)))
    (hPrem : eo_interprets M (mkEq y (mkSetEmpty T)) true) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkSetMember x y)))
      (__smtx_model_eval M (__eo_to_smt (Term.Boolean false))) := by
  have hEmptyTy :
      __smtx_typeof (__eo_to_smt (mkSetEmpty T)) =
        SmtType.Set (__eo_to_smt_type T) :=
    smt_typeof_mkSetEmpty_of_set_type_wf T hTypeWf
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      y (mkSetEmpty T) hPremBool with
    ⟨hYEmptyTy, _hYNonNone⟩
  have hYSmtTyT :
      __smtx_typeof (__eo_to_smt y) = SmtType.Set (__eo_to_smt_type T) :=
    hYEmptyTy.trans hEmptyTy
  have hSetNonNone :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T) ≠
        SmtType.None :=
    Smtm.type_wf_non_none hTypeWf
  have hTNonNone : __eo_to_smt_type T ≠ SmtType.None :=
    eo_to_smt_type_set_component_non_none T hSetNonNone
  have hYEval := set_eval_eq_empty_of_premise M hM y T hYSmtTyT
    hTNonNone hPrem
  unfold mkSetMember
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M
      (SmtTerm.set_member (__eo_to_smt x) (__eo_to_smt y)))
    (__smtx_model_eval M (SmtTerm.Boolean false))
  simp [__smtx_model_eval, __smtx_model_eval_set_member, __smtx_map_select,
    hYEval, __smtx_map_lookup]
  exact RuleProofs.smt_value_rel_refl (SmtValue.Boolean false)

theorem facts_set_member_empty_false
    (M : SmtModel) (hM : model_wf M)
    (x y T : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hyTrans : RuleProofs.eo_has_smt_translation y)
    (hTypeWf :
      __smtx_type_wf
        (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T)) = true)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq y (mkSetEmpty T)))
    (hFormulaTy :
      __eo_typeof (mkEq (mkSetMember x y) (Term.Boolean false)) =
        Term.Bool)
    (hPrem : eo_interprets M (mkEq y (mkSetEmpty T)) true) :
    eo_interprets M (mkEq (mkSetMember x y) (Term.Boolean false)) true := by
  exact RuleProofs.eo_interprets_eq_of_rel M (mkSetMember x y)
    (Term.Boolean false)
    (typed_set_member_eq_false x y hxTrans hyTrans hFormulaTy)
    (set_member_empty_rel_of_premise_bool M hM x y T hyTrans hTypeWf
      hPremBool hPrem)

private theorem smtx_model_eval_eq_false_of_ne_not_reglan
    {v₁ v₂ : SmtValue}
    (hNe : v₁ ≠ v₂)
    (hReg :
      ¬ ∃ r₁ r₂, v₁ = SmtValue.RegLan r₁ ∧ v₂ = SmtValue.RegLan r₂) :
    __smtx_model_eval_eq v₁ v₂ = SmtValue.Boolean false := by
  cases v₁ <;> cases v₂ <;>
    simp [__smtx_model_eval_eq, native_veq] at hNe hReg ⊢
  all_goals exact hNe

private theorem set_empty_value_set_singleton_value_model_eval_eq_false
    (T : SmtType) (v : SmtValue) :
    __smtx_model_eval_eq
        (SmtValue.Set (SmtMap.default T (SmtValue.Boolean false)))
        (__smtx_model_eval_set_singleton v) =
      SmtValue.Boolean false := by
  apply smtx_model_eval_eq_false_of_ne_not_reglan
  · intro hEq
    simp [__smtx_model_eval_set_singleton] at hEq
  · rintro ⟨r₁, r₂, hReg₁, _hReg₂⟩
    cases hReg₁

theorem eo_typeof_eq_false_inner_bool_info
    {inner : Term}
    (hTy : __eo_typeof (mkEq inner (Term.Boolean false)) = Term.Bool) :
    __eo_typeof inner = Term.Bool := by
  have hEqTy :
      __eo_typeof_eq (__eo_typeof inner) Term.Bool = Term.Bool := by
    have hsimpa := hTy
    try simp [mkEq] at hsimpa ⊢
    exact hsimpa
  exact (SetsMemberSupport.eo_typeof_eq_eq_bool_info hEqTy).1

theorem eo_typeof_set_eq_singleton_bool_info
    {x y : Term}
    (hTy : __eo_typeof (mkEq x (mkSetSingleton y)) = Term.Bool) :
    ∃ T : Term,
      __eo_typeof x = Term.Apply (Term.UOp UserOp.Set) T ∧
        __eo_typeof y = T := by
  have hEqTy :
      __eo_typeof_eq (__eo_typeof x) (__eo_typeof (mkSetSingleton y)) =
        Term.Bool := by
    have hsimpa := hTy
    try simp [mkEq] at hsimpa ⊢
    exact hsimpa
  rcases SetsMemberSupport.eo_typeof_eq_eq_bool_info hEqTy with
    ⟨hSame, hXNotStuck⟩
  change __eo_typeof x = __eo_typeof_set_singleton (__eo_typeof y) at hSame
  by_cases hyStuck : __eo_typeof y = Term.Stuck
  · exfalso
    apply hXNotStuck
    simpa [mkSetSingleton, __eo_typeof_set_singleton, hyStuck] using hSame
  · refine ⟨__eo_typeof y, ?_, rfl⟩
    simpa [mkSetSingleton, __eo_typeof_set_singleton, hyStuck] using hSame

theorem typed_set_eq_singleton
    (x y : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hyTrans : RuleProofs.eo_has_smt_translation y)
    (hTy : __eo_typeof (mkEq x (mkSetSingleton y)) = Term.Bool) :
    RuleProofs.eo_has_bool_type (mkEq x (mkSetSingleton y)) := by
  rcases eo_typeof_set_eq_singleton_bool_info (x := x) (y := y) hTy with
    ⟨T, hxTy, hyTy⟩
  have hxMatch :
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hxTrans
  have hyMatch :
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation y hyTrans
  have hSetNonNone :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T) ≠
        SmtType.None := by
    have hRaw : __eo_to_smt_type (__eo_typeof x) ≠ SmtType.None := by
      rw [← hxMatch]
      exact hxTrans
    simpa [hxTy] using hRaw
  have hSetTy :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T) =
        SmtType.Set (__eo_to_smt_type T) :=
    eo_to_smt_type_set_of_non_none T hSetNonNone
  have hXSmtTy :
      __smtx_typeof (__eo_to_smt x) = SmtType.Set (__eo_to_smt_type T) := by
    simpa [hxTy, hSetTy] using hxMatch
  have hYSmtTy :
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type T := by
    simpa [hyTy] using hyMatch
  have hSetWf : __smtx_type_wf (SmtType.Set (__eo_to_smt_type T)) = true :=
    Smtm.smt_term_set_type_wf_of_non_none
      (__eo_to_smt x)
      (by
        unfold term_has_non_none_type
        rw [hXSmtTy]
        simp)
      hXSmtTy
  have hSingletonTy :
      __smtx_typeof (__eo_to_smt (mkSetSingleton y)) =
        SmtType.Set (__eo_to_smt_type T) := by
    change __smtx_typeof (SmtTerm.set_singleton (__eo_to_smt y)) =
      SmtType.Set (__eo_to_smt_type T)
    rw [smtx_typeof_set_singleton_term_eq, hYSmtTy]
    simp [__smtx_typeof_guard_wf, hSetWf, native_ite]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type x (mkSetSingleton y)
    (by rw [hXSmtTy, hSingletonTy])
    (by rw [hXSmtTy]; simp)

theorem typed_set_eq_singleton_emp
    (x y : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hyTrans : RuleProofs.eo_has_smt_translation y)
    (hTy :
      __eo_typeof (mkEq (mkEq x (mkSetSingleton y)) (Term.Boolean false)) =
        Term.Bool) :
    RuleProofs.eo_has_bool_type
      (mkEq (mkEq x (mkSetSingleton y)) (Term.Boolean false)) := by
  have hInnerTy :
      __eo_typeof (mkEq x (mkSetSingleton y)) = Term.Bool :=
    eo_typeof_eq_false_inner_bool_info hTy
  have hInnerBool :
      RuleProofs.eo_has_bool_type (mkEq x (mkSetSingleton y)) :=
    typed_set_eq_singleton x y hxTrans hyTrans hInnerTy
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (mkEq x (mkSetSingleton y)) (Term.Boolean false)
    (by rw [hInnerBool, RuleProofs.eo_to_smt_false_eq, __smtx_typeof.eq_1])
    (by rw [hInnerBool]; simp)

theorem set_eq_singleton_emp_rel_of_premise_bool
    (M : SmtModel) (hM : model_wf M)
    (x y T : Term)
    (hTypeWf :
      __smtx_type_wf
        (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T)) = true)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq x (mkSetEmpty T)))
    (hPrem : eo_interprets M (mkEq x (mkSetEmpty T)) true) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkEq x (mkSetSingleton y))))
      (__smtx_model_eval M (__eo_to_smt (Term.Boolean false))) := by
  have hEmptyTy :
      __smtx_typeof (__eo_to_smt (mkSetEmpty T)) =
        SmtType.Set (__eo_to_smt_type T) :=
    smt_typeof_mkSetEmpty_of_set_type_wf T hTypeWf
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      x (mkSetEmpty T) hPremBool with
    ⟨hXEmptyTy, _hXNonNone⟩
  have hXSmtTyT :
      __smtx_typeof (__eo_to_smt x) = SmtType.Set (__eo_to_smt_type T) :=
    hXEmptyTy.trans hEmptyTy
  have hSetNonNone :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T) ≠
        SmtType.None :=
    Smtm.type_wf_non_none hTypeWf
  have hTNonNone : __eo_to_smt_type T ≠ SmtType.None :=
    eo_to_smt_type_set_component_non_none T hSetNonNone
  have hXEval := set_eval_eq_empty_of_premise M hM x T hXSmtTyT
    hTNonNone hPrem
  have hInnerFalse :
      __smtx_model_eval_eq
          (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval M (__eo_to_smt (mkSetSingleton y))) =
        SmtValue.Boolean false := by
    change __smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (SmtTerm.set_singleton (__eo_to_smt y))) =
      SmtValue.Boolean false
    rw [hXEval, smtx_eval_set_singleton_term_eq]
    exact set_empty_value_set_singleton_value_model_eval_eq_false
      (__eo_to_smt_type T) (__smtx_model_eval M (__eo_to_smt y))
  change
    __smtx_model_eval_eq
      (__smtx_model_eval M (__eo_to_smt (mkEq x (mkSetSingleton y))))
      (__smtx_model_eval M (__eo_to_smt (Term.Boolean false))) =
        SmtValue.Boolean true
  change
    __smtx_model_eval_eq
      (__smtx_model_eval M
        (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt (mkSetSingleton y))))
      (__smtx_model_eval M (SmtTerm.Boolean false)) =
        SmtValue.Boolean true
  rw [smtx_eval_eq_term_eq, __smtx_model_eval.eq_1, hInnerFalse]
  exact RuleProofs.smtx_model_eval_eq_refl (SmtValue.Boolean false)

theorem facts_set_eq_singleton_emp_false
    (M : SmtModel) (hM : model_wf M)
    (x y T : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hyTrans : RuleProofs.eo_has_smt_translation y)
    (hTypeWf :
      __smtx_type_wf
        (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T)) = true)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq x (mkSetEmpty T)))
    (hFormulaTy :
      __eo_typeof (mkEq (mkEq x (mkSetSingleton y)) (Term.Boolean false)) =
        Term.Bool)
    (hPrem : eo_interprets M (mkEq x (mkSetEmpty T)) true) :
    eo_interprets M
      (mkEq (mkEq x (mkSetSingleton y)) (Term.Boolean false)) true := by
  exact RuleProofs.eo_interprets_eq_of_rel M (mkEq x (mkSetSingleton y))
    (Term.Boolean false)
    (typed_set_eq_singleton_emp x y hxTrans hyTrans hFormulaTy)
    (set_eq_singleton_emp_rel_of_premise_bool M hM x y T hTypeWf
      hPremBool hPrem)

theorem prog_sets_eq_singleton_emp_info
    (x y ty P : Term)
    (hProg :
      __eo_prog_sets_eq_singleton_emp x y ty (Proof.pf P) ≠ Term.Stuck) :
    ∃ T x0 T0 : Term,
      ty = Term.Apply (Term.UOp UserOp.Set) T ∧
        P = mkEq x0 (mkSetEmpty T0) ∧
          x0 = x ∧
            T0 = T ∧
              __eo_prog_sets_eq_singleton_emp x y ty (Proof.pf P) =
                mkEq (mkEq x (mkSetSingleton y)) (Term.Boolean false) := by
  by_cases hx : x = Term.Stuck
  · subst x
    simp [__eo_prog_sets_eq_singleton_emp] at hProg
  by_cases hy : y = Term.Stuck
  · subst y
    simp [__eo_prog_sets_eq_singleton_emp, hx] at hProg
  cases ty with
  | Apply f T =>
      cases f with
      | UOp op =>
          by_cases hSet : op = UserOp.Set
          · subst op
            cases P with
            | Apply pf rhs =>
                cases pf with
                | Apply pg x0 =>
                    cases pg with
                    | UOp eqOp =>
                        by_cases hEq : eqOp = UserOp.eq
                        · subst eqOp
                          cases rhs with
                          | UOp1 emptyOp setTy =>
                              by_cases hEmpty : emptyOp = UserOp1.set_empty
                              · subst emptyOp
                                cases setTy with
                                | Apply setF T0 =>
                                    cases setF with
                                    | UOp setOp =>
                                        by_cases hSetTy : setOp = UserOp.Set
                                        · subst setOp
                                          let B :=
                                            mkEq (mkEq x (mkSetSingleton y))
                                              (Term.Boolean false)
                                          have hReq :
                                              __eo_requires
                                                  (__eo_and (__eo_eq x x0)
                                                    (__eo_eq T T0))
                                                  (Term.Boolean true) B ≠
                                                Term.Stuck := by
                                            simpa [B,
                                              __eo_prog_sets_eq_singleton_emp,
                                              hx, hy, mkEq, mkSetSingleton,
                                              mkSetEmpty] using hProg
                                          have hEqs :
                                              x0 = x ∧ T0 = T :=
                                            RuleProofs.eqs_of_requires_and_eq_true_not_stuck
                                              x T x0 T0 B hReq
                                          have hUnfold :
                                              __eo_prog_sets_eq_singleton_emp
                                                  x y
                                                  (Term.Apply
                                                    (Term.UOp UserOp.Set) T)
                                                  (Proof.pf
                                                    (mkEq x0
                                                      (mkSetEmpty T0))) =
                                                __eo_requires
                                                  (__eo_and (__eo_eq x x0)
                                                    (__eo_eq T T0))
                                                  (Term.Boolean true) B := by
                                            simp [B,
                                              __eo_prog_sets_eq_singleton_emp,
                                              hx, hy, mkEq, mkSetSingleton,
                                              mkSetEmpty]
                                          refine ⟨T, x0, T0, rfl, rfl,
                                            hEqs.1, hEqs.2, ?_⟩
                                          change
                                            __eo_prog_sets_eq_singleton_emp x y
                                                (Term.Apply
                                                  (Term.UOp UserOp.Set) T)
                                                (Proof.pf
                                                  (mkEq x0
                                                    (mkSetEmpty T0))) =
                                              mkEq (mkEq x (mkSetSingleton y))
                                                (Term.Boolean false)
                                          rw [hUnfold,
                                            SetsEvalOpSupport.req_result hReq]
                                        · exfalso
                                          apply hProg
                                          simp [__eo_prog_sets_eq_singleton_emp,
                                            hx, hy, hSetTy, mkEq, mkSetEmpty]
                                    | _ =>
                                        exfalso
                                        apply hProg
                                        simp [__eo_prog_sets_eq_singleton_emp,
                                          hx, hy, mkEq, mkSetEmpty]
                                | _ =>
                                    exfalso
                                    apply hProg
                                    simp [__eo_prog_sets_eq_singleton_emp,
                                      hx, hy, mkEq, mkSetEmpty]
                              · exfalso
                                apply hProg
                                simp [__eo_prog_sets_eq_singleton_emp, hx, hy,
                                  hEmpty, mkEq, mkSetEmpty]
                          | _ =>
                              exfalso
                              apply hProg
                              simp [__eo_prog_sets_eq_singleton_emp, hx, hy,
                                mkEq, mkSetEmpty]
                        · exfalso
                          apply hProg
                          simp [__eo_prog_sets_eq_singleton_emp, hx, hy, hEq,
                            mkEq, mkSetEmpty]
                    | _ =>
                        exfalso
                        apply hProg
                        simp [__eo_prog_sets_eq_singleton_emp, hx, hy, mkEq,
                          mkSetEmpty]
                | _ =>
                    exfalso
                    apply hProg
                    simp [__eo_prog_sets_eq_singleton_emp, hx, hy, mkEq,
                      mkSetEmpty]
            | _ =>
                exfalso
                apply hProg
                simp [__eo_prog_sets_eq_singleton_emp, hx, hy, mkEq,
                  mkSetEmpty]
          · exfalso
            apply hProg
            simp [__eo_prog_sets_eq_singleton_emp, hx, hy, hSet]
      | _ =>
          exfalso
          apply hProg
          simp [__eo_prog_sets_eq_singleton_emp, hx, hy]
  | _ =>
      exfalso
      apply hProg
      simp [__eo_prog_sets_eq_singleton_emp, hx, hy]

theorem prog_sets_member_emp_info
    (x y ty P : Term)
    (hProg :
      __eo_prog_sets_member_emp x y ty (Proof.pf P) ≠ Term.Stuck) :
    ∃ T y0 T0 : Term,
      ty = Term.Apply (Term.UOp UserOp.Set) T ∧
        P = mkEq y0 (mkSetEmpty T0) ∧
          y0 = y ∧
            T0 = T ∧
              __eo_prog_sets_member_emp x y ty (Proof.pf P) =
                mkEq (mkSetMember x y) (Term.Boolean false) := by
  by_cases hx : x = Term.Stuck
  · subst x
    simp [__eo_prog_sets_member_emp] at hProg
  by_cases hy : y = Term.Stuck
  · subst y
    simp [__eo_prog_sets_member_emp, hx] at hProg
  cases ty with
  | Apply f T =>
      cases f with
      | UOp op =>
          by_cases hSet : op = UserOp.Set
          · subst op
            cases P with
            | Apply pf rhs =>
                cases pf with
                | Apply pg y0 =>
                    cases pg with
                    | UOp eqOp =>
                        by_cases hEq : eqOp = UserOp.eq
                        · subst eqOp
                          cases rhs with
                          | UOp1 emptyOp setTy =>
                              by_cases hEmpty : emptyOp = UserOp1.set_empty
                              · subst emptyOp
                                cases setTy with
                                | Apply setF T0 =>
                                    cases setF with
                                    | UOp setOp =>
                                        by_cases hSetTy : setOp = UserOp.Set
                                        · subst setOp
                                          let B := mkEq (mkSetMember x y)
                                            (Term.Boolean false)
                                          have hReq :
                                              __eo_requires
                                                  (__eo_and (__eo_eq y y0)
                                                    (__eo_eq T T0))
                                                  (Term.Boolean true) B ≠
                                                Term.Stuck := by
                                            simpa [B, __eo_prog_sets_member_emp,
                                              hx, hy, mkEq, mkSetMember,
                                              mkSetEmpty] using hProg
                                          have hEqs :
                                              y0 = y ∧ T0 = T :=
                                            RuleProofs.eqs_of_requires_and_eq_true_not_stuck
                                              y T y0 T0 B hReq
                                          have hUnfold :
                                              __eo_prog_sets_member_emp x y
                                                  (Term.Apply
                                                    (Term.UOp UserOp.Set) T)
                                                  (Proof.pf
                                                    (mkEq y0 (mkSetEmpty T0))) =
                                                __eo_requires
                                                  (__eo_and (__eo_eq y y0)
                                                    (__eo_eq T T0))
                                                  (Term.Boolean true) B := by
                                            simp [B, __eo_prog_sets_member_emp,
                                              hx, hy, mkEq, mkSetMember,
                                              mkSetEmpty]
                                          refine ⟨T, y0, T0, rfl, rfl,
                                            hEqs.1, hEqs.2, ?_⟩
                                          change
                                            __eo_prog_sets_member_emp x y
                                                (Term.Apply
                                                  (Term.UOp UserOp.Set) T)
                                                (Proof.pf
                                                  (mkEq y0 (mkSetEmpty T0))) =
                                              mkEq (mkSetMember x y)
                                                (Term.Boolean false)
                                          rw [hUnfold, SetsEvalOpSupport.req_result hReq]
                                        · exfalso
                                          apply hProg
                                          simp [__eo_prog_sets_member_emp, hx,
                                            hy, hSetTy, mkEq, mkSetEmpty]
                                    | _ =>
                                        exfalso
                                        apply hProg
                                        simp [__eo_prog_sets_member_emp, hx,
                                          hy, mkEq, mkSetEmpty]
                                | _ =>
                                    exfalso
                                    apply hProg
                                    simp [__eo_prog_sets_member_emp, hx, hy,
                                      mkEq, mkSetEmpty]
                              · exfalso
                                apply hProg
                                simp [__eo_prog_sets_member_emp, hx, hy,
                                  hEmpty, mkEq, mkSetEmpty]
                          | _ =>
                              exfalso
                              apply hProg
                              simp [__eo_prog_sets_member_emp, hx, hy, mkEq,
                                mkSetEmpty]
                        · exfalso
                          apply hProg
                          simp [__eo_prog_sets_member_emp, hx, hy, hEq, mkEq,
                            mkSetEmpty]
                    | _ =>
                        exfalso
                        apply hProg
                        simp [__eo_prog_sets_member_emp, hx, hy, mkEq,
                          mkSetEmpty]
                | _ =>
                    exfalso
                    apply hProg
                    simp [__eo_prog_sets_member_emp, hx, hy, mkEq, mkSetEmpty]
            | _ =>
                exfalso
                apply hProg
                simp [__eo_prog_sets_member_emp, hx, hy, mkEq, mkSetEmpty]
          · exfalso
            apply hProg
            simp [__eo_prog_sets_member_emp, hx, hy, hSet]
      | _ =>
          exfalso
          apply hProg
          simp [__eo_prog_sets_member_emp, hx, hy]
  | _ =>
      exfalso
      apply hProg
      simp [__eo_prog_sets_member_emp, hx, hy]

theorem eo_typeof_set_inter_bool_info
    {x y rhs : Term}
    (hTy : __eo_typeof (mkEq (mkSetInter x y) rhs) = Term.Bool) :
    ∃ T : Term,
      __eo_typeof x = Term.Apply (Term.UOp UserOp.Set) T ∧
        __eo_typeof y = Term.Apply (Term.UOp UserOp.Set) T ∧
          __eo_typeof rhs = Term.Apply (Term.UOp UserOp.Set) T := by
  have hEqTy :
      __eo_typeof_eq
        (__eo_typeof_set_union (__eo_typeof x) (__eo_typeof y))
        (__eo_typeof rhs) = Term.Bool := by
    have hsimpa := hTy
    try simp [mkEq, mkSetInter] at hsimpa ⊢
    exact hsimpa
  rcases SetsMemberSupport.eo_typeof_eq_eq_bool_info hEqTy with
    ⟨hSame, hInterNS⟩
  rcases eo_typeof_set_union_ne_stuck_info hInterNS with
    ⟨T, hxTy, hyTy, hInterTy⟩
  exact ⟨T, hxTy, hyTy, by rw [← hSame, hInterTy]⟩

theorem eo_typeof_set_minus_bool_info
    {x y rhs : Term}
    (hTy : __eo_typeof (mkEq (mkSetMinus x y) rhs) = Term.Bool) :
    ∃ T : Term,
      __eo_typeof x = Term.Apply (Term.UOp UserOp.Set) T ∧
        __eo_typeof y = Term.Apply (Term.UOp UserOp.Set) T ∧
          __eo_typeof rhs = Term.Apply (Term.UOp UserOp.Set) T := by
  have hEqTy :
      __eo_typeof_eq
        (__eo_typeof_set_union (__eo_typeof x) (__eo_typeof y))
        (__eo_typeof rhs) = Term.Bool := by
    have hsimpa := hTy
    try simp [mkEq, mkSetMinus] at hsimpa ⊢
    exact hsimpa
  rcases SetsMemberSupport.eo_typeof_eq_eq_bool_info hEqTy with
    ⟨hSame, hMinusNS⟩
  rcases eo_typeof_set_union_ne_stuck_info hMinusNS with
    ⟨T, hxTy, hyTy, hMinusTy⟩
  exact ⟨T, hxTy, hyTy, by rw [← hSame, hMinusTy]⟩

theorem typed_set_inter_eq_right
    (x y rhs : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hyTrans : RuleProofs.eo_has_smt_translation y)
    (hrhsTrans : RuleProofs.eo_has_smt_translation rhs)
    (hTy : __eo_typeof (mkEq (mkSetInter x y) rhs) = Term.Bool) :
    RuleProofs.eo_has_bool_type (mkEq (mkSetInter x y) rhs) := by
  rcases eo_typeof_set_inter_bool_info (x := x) (y := y) (rhs := rhs) hTy with
    ⟨T, hxTy, hyTy, hrhsTy⟩
  rcases set_smt_types_of_eo_set_types hxTrans hyTrans hxTy hyTy with
    ⟨hxSmtTy, hySmtTy, _hTNonNone⟩
  rcases set_smt_types_of_eo_set_types hxTrans hrhsTrans hxTy hrhsTy with
    ⟨_hxSmtTy', hrhsSmtTy, _⟩
  have hSetWf : __smtx_type_wf (SmtType.Set (__eo_to_smt_type T)) = true :=
    Smtm.smt_term_set_type_wf_of_non_none
      (__eo_to_smt y)
      (by
        unfold term_has_non_none_type
        rw [hySmtTy]
        simp)
      hySmtTy
  unfold RuleProofs.eo_has_bool_type
  change
    __smtx_typeof
        (SmtTerm.eq (SmtTerm.set_inter (__eo_to_smt x) (__eo_to_smt y))
          (__eo_to_smt rhs)) = SmtType.Bool
  rw [typeof_eq_eq, typeof_set_inter_eq]
  simp [__smtx_typeof_sets_op_2, __smtx_typeof_eq, native_ite, native_Teq,
    __smtx_typeof_guard, hxSmtTy, hySmtTy, hrhsSmtTy, hSetWf]

theorem typed_set_minus_eq_right
    (x y rhs : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hyTrans : RuleProofs.eo_has_smt_translation y)
    (hrhsTrans : RuleProofs.eo_has_smt_translation rhs)
    (hTy : __eo_typeof (mkEq (mkSetMinus x y) rhs) = Term.Bool) :
    RuleProofs.eo_has_bool_type (mkEq (mkSetMinus x y) rhs) := by
  rcases eo_typeof_set_minus_bool_info (x := x) (y := y) (rhs := rhs) hTy with
    ⟨T, hxTy, hyTy, hrhsTy⟩
  rcases set_smt_types_of_eo_set_types hxTrans hyTrans hxTy hyTy with
    ⟨hxSmtTy, hySmtTy, _hTNonNone⟩
  rcases set_smt_types_of_eo_set_types hxTrans hrhsTrans hxTy hrhsTy with
    ⟨_hxSmtTy', hrhsSmtTy, _⟩
  have hSetWf : __smtx_type_wf (SmtType.Set (__eo_to_smt_type T)) = true :=
    Smtm.smt_term_set_type_wf_of_non_none
      (__eo_to_smt y)
      (by
        unfold term_has_non_none_type
        rw [hySmtTy]
        simp)
      hySmtTy
  unfold RuleProofs.eo_has_bool_type
  change
    __smtx_typeof
        (SmtTerm.eq (SmtTerm.set_minus (__eo_to_smt x) (__eo_to_smt y))
          (__eo_to_smt rhs)) = SmtType.Bool
  rw [typeof_eq_eq, typeof_set_minus_eq]
  simp [__smtx_typeof_sets_op_2, __smtx_typeof_eq, native_ite, native_Teq,
    __smtx_typeof_guard, hxSmtTy, hySmtTy, hrhsSmtTy, hSetWf]

theorem set_inter_empty_left_rel_of_premise_bool
    (M : SmtModel) (hM : model_wf M)
    (x y T : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hyTrans : RuleProofs.eo_has_smt_translation y)
    (hTypeWf :
      __smtx_type_wf
        (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T)) = true)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq x (mkSetEmpty T)))
    (hFormulaTy : __eo_typeof (mkEq (mkSetInter x y) x) = Term.Bool)
    (hPrem : eo_interprets M (mkEq x (mkSetEmpty T)) true) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkSetInter x y)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  rcases eo_typeof_set_inter_bool_info (x := x) (y := y) (rhs := x)
      hFormulaTy with
    ⟨U, hxTy, hyTy, _hxTy'⟩
  rcases set_smt_types_of_eo_set_types hxTrans hyTrans hxTy hyTy with
    ⟨hXSmtTyU, hYSmtTyU, _hUNonNone⟩
  have hEmptyTy :
      __smtx_typeof (__eo_to_smt (mkSetEmpty T)) =
        SmtType.Set (__eo_to_smt_type T) :=
    smt_typeof_mkSetEmpty_of_set_type_wf T hTypeWf
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      x (mkSetEmpty T) hPremBool with
    ⟨hXEmptyTy, _hXNonNone⟩
  have hXSmtTyT :
      __smtx_typeof (__eo_to_smt x) = SmtType.Set (__eo_to_smt_type T) :=
    hXEmptyTy.trans hEmptyTy
  have hElemTy : __eo_to_smt_type U = __eo_to_smt_type T := by
    rw [hXSmtTyT] at hXSmtTyU
    injection hXSmtTyU with hEq
    exact hEq.symm
  have hYSmtTyT :
      __smtx_typeof (__eo_to_smt y) = SmtType.Set (__eo_to_smt_type T) := by
    simpa [hElemTy] using hYSmtTyU
  have hSetNonNone :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T) ≠
        SmtType.None :=
    Smtm.type_wf_non_none hTypeWf
  have hTNonNone : __eo_to_smt_type T ≠ SmtType.None :=
    eo_to_smt_type_set_component_non_none T hSetNonNone
  have hXEval := set_eval_eq_empty_of_premise M hM x T hXSmtTyT
    hTNonNone hPrem
  rcases set_value_facts M hM y (__eo_to_smt_type T) hyTrans hYSmtTyT with
    ⟨my, hYEval, _hYCan, _hYTy, _hYDef⟩
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M
      (SmtTerm.set_inter (__eo_to_smt x) (__eo_to_smt y)))
    (__smtx_model_eval M (__eo_to_smt x))
  rw [model_eval_inter_eq M (__eo_to_smt x) (__eo_to_smt y), hXEval,
    hYEval]
  change RuleProofs.smt_value_rel
    (__smtx_set_inter
      (SmtValue.Set
        (SmtMap.default (__eo_to_smt_type T) (SmtValue.Boolean false)))
      (SmtValue.Set my))
    (SmtValue.Set
      (SmtMap.default (__eo_to_smt_type T) (SmtValue.Boolean false)))
  simp [__smtx_set_inter, __smtx_set_op_rec, __smtx_index_typeof_map,
    __smtx_typeof_map_value, __smtx_typeof_value]
  exact RuleProofs.smt_value_rel_refl
    (SmtValue.Set
      (SmtMap.default (__eo_to_smt_type T) (SmtValue.Boolean false)))

theorem set_minus_empty_left_rel_of_premise_bool
    (M : SmtModel) (hM : model_wf M)
    (x y T : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hyTrans : RuleProofs.eo_has_smt_translation y)
    (hTypeWf :
      __smtx_type_wf
        (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T)) = true)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq x (mkSetEmpty T)))
    (hFormulaTy : __eo_typeof (mkEq (mkSetMinus x y) x) = Term.Bool)
    (hPrem : eo_interprets M (mkEq x (mkSetEmpty T)) true) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkSetMinus x y)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  rcases eo_typeof_set_minus_bool_info (x := x) (y := y) (rhs := x)
      hFormulaTy with
    ⟨U, hxTy, hyTy, _hxTy'⟩
  rcases set_smt_types_of_eo_set_types hxTrans hyTrans hxTy hyTy with
    ⟨hXSmtTyU, hYSmtTyU, _hUNonNone⟩
  have hEmptyTy :
      __smtx_typeof (__eo_to_smt (mkSetEmpty T)) =
        SmtType.Set (__eo_to_smt_type T) :=
    smt_typeof_mkSetEmpty_of_set_type_wf T hTypeWf
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      x (mkSetEmpty T) hPremBool with
    ⟨hXEmptyTy, _hXNonNone⟩
  have hXSmtTyT :
      __smtx_typeof (__eo_to_smt x) = SmtType.Set (__eo_to_smt_type T) :=
    hXEmptyTy.trans hEmptyTy
  have hElemTy : __eo_to_smt_type U = __eo_to_smt_type T := by
    rw [hXSmtTyT] at hXSmtTyU
    injection hXSmtTyU with hEq
    exact hEq.symm
  have hYSmtTyT :
      __smtx_typeof (__eo_to_smt y) = SmtType.Set (__eo_to_smt_type T) := by
    simpa [hElemTy] using hYSmtTyU
  have hSetNonNone :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T) ≠
        SmtType.None :=
    Smtm.type_wf_non_none hTypeWf
  have hTNonNone : __eo_to_smt_type T ≠ SmtType.None :=
    eo_to_smt_type_set_component_non_none T hSetNonNone
  have hXEval := set_eval_eq_empty_of_premise M hM x T hXSmtTyT
    hTNonNone hPrem
  rcases set_value_facts M hM y (__eo_to_smt_type T) hyTrans hYSmtTyT with
    ⟨my, hYEval, _hYCan, _hYTy, _hYDef⟩
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M
      (SmtTerm.set_minus (__eo_to_smt x) (__eo_to_smt y)))
    (__smtx_model_eval M (__eo_to_smt x))
  rw [model_eval_minus_eq M (__eo_to_smt x) (__eo_to_smt y), hXEval,
    hYEval]
  change RuleProofs.smt_value_rel
    (__smtx_set_minus
      (SmtValue.Set
        (SmtMap.default (__eo_to_smt_type T) (SmtValue.Boolean false)))
      (SmtValue.Set my))
    (SmtValue.Set
      (SmtMap.default (__eo_to_smt_type T) (SmtValue.Boolean false)))
  simp [__smtx_set_minus, __smtx_set_op_rec, __smtx_index_typeof_map,
    __smtx_typeof_map_value, __smtx_typeof_value]
  exact RuleProofs.smt_value_rel_refl
    (SmtValue.Set
      (SmtMap.default (__eo_to_smt_type T) (SmtValue.Boolean false)))

theorem set_union_empty_right_rel_of_premise_bool
    (M : SmtModel) (hM : model_wf M)
    (x y T : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hyTrans : RuleProofs.eo_has_smt_translation y)
    (hTypeWf :
      __smtx_type_wf
        (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T)) = true)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq y (mkSetEmpty T)))
    (hFormulaTy : __eo_typeof (mkEq (mkSetUnion x y) x) = Term.Bool)
    (hPrem : eo_interprets M (mkEq y (mkSetEmpty T)) true) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkSetUnion x y)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  rcases eo_typeof_set_union_bool_info (x := x) (y := y) (rhs := x)
      hFormulaTy with
    ⟨U, hxTy, hyTy, _hxTy'⟩
  rcases set_smt_types_of_eo_set_types hxTrans hyTrans hxTy hyTy with
    ⟨hXSmtTyU, hYSmtTyU, _hUNonNone⟩
  have hEmptyTy :
      __smtx_typeof (__eo_to_smt (mkSetEmpty T)) =
        SmtType.Set (__eo_to_smt_type T) :=
    smt_typeof_mkSetEmpty_of_set_type_wf T hTypeWf
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      y (mkSetEmpty T) hPremBool with
    ⟨hYEmptyTy, _hYNonNone⟩
  have hYSmtTyT :
      __smtx_typeof (__eo_to_smt y) = SmtType.Set (__eo_to_smt_type T) :=
    hYEmptyTy.trans hEmptyTy
  have hElemTy : __eo_to_smt_type U = __eo_to_smt_type T := by
    rw [hYSmtTyT] at hYSmtTyU
    injection hYSmtTyU with hEq
    exact hEq.symm
  have hXSmtTyT :
      __smtx_typeof (__eo_to_smt x) = SmtType.Set (__eo_to_smt_type T) := by
    simpa [hElemTy] using hXSmtTyU
  have hSetNonNone :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T) ≠
        SmtType.None :=
    Smtm.type_wf_non_none hTypeWf
  have hTNonNone : __eo_to_smt_type T ≠ SmtType.None :=
    eo_to_smt_type_set_component_non_none T hSetNonNone
  have hYEval := set_eval_eq_empty_of_premise M hM y T hYSmtTyT
    hTNonNone hPrem
  rcases set_value_facts M hM x (__eo_to_smt_type T) hxTrans hXSmtTyT with
    ⟨mx, hXEval, hMxCan, hMxTy, hMxDef⟩
  let empty :=
    SmtMap.default (__eo_to_smt_type T) (SmtValue.Boolean false)
  let acc :=
    SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value mx))
      (SmtValue.Boolean false)
  let res := __smtx_set_op_rec false mx acc empty
  have hEmptyTyMap :
      __smtx_typeof_map_value empty =
        SmtType.Map (__eo_to_smt_type T) SmtType.Bool := by
    dsimp [empty]
    simp [__smtx_typeof_map_value, __smtx_typeof_value]
  have hEmptyCan : __smtx_map_canonical empty = true := by
    dsimp [empty]
    exact set_empty_map_canonical' (__eo_to_smt_type T)
  have hEmptyDef : __smtx_map_get_default empty = SmtValue.Boolean false := by
    dsimp [empty]
    simp [__smtx_map_get_default]
  have hAccTy :
      __smtx_typeof_map_value acc =
        SmtType.Map (__eo_to_smt_type T) SmtType.Bool := by
    dsimp [acc]
    rw [hMxTy]
    simp [__smtx_index_typeof_map, __smtx_typeof_map_value,
      __smtx_typeof_value]
  have hResCan : __smtx_map_canonical res = true := by
    dsimp [res]
    exact Smtm.mss_op_internal_canonical false hMxCan hEmptyCan
  have hResTy :
      __smtx_typeof_map_value res =
        SmtType.Map (__eo_to_smt_type T) SmtType.Bool := by
    dsimp [res]
    exact Smtm.mss_op_internal_typed false hMxTy hAccTy hEmptyTyMap
  have hResDef : __smtx_map_get_default res = SmtValue.Boolean false := by
    dsimp [res]
    rw [Smtm.mss_op_internal_get_default]
    exact hEmptyDef
  have hLeaf : smt_map_default_leaf res = smt_map_default_leaf mx := by
    rw [set_default_leaf hResCan hResTy hResDef,
      set_default_leaf hMxCan hMxTy hMxDef]
  have hLookup :
      ∀ v : SmtValue,
        __smtx_map_lookup res v = __smtx_map_lookup mx v := by
    intro v
    dsimp [res, acc]
    rw [set_union_lookup mx empty (__eo_to_smt_type T) v hMxTy
      hEmptyTyMap hMxCan hEmptyCan hMxDef]
    simpa [empty, __smtx_map_lookup] using
      set_map_lookup_bool_ite_true_false
        (m := mx) (A := __eo_to_smt_type T) v hMxTy hMxCan hMxDef
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M
      (SmtTerm.set_union (__eo_to_smt x) (__eo_to_smt y)))
    (__smtx_model_eval M (__eo_to_smt x))
  rw [model_eval_union_eq M (__eo_to_smt x) (__eo_to_smt y), hXEval,
    hYEval]
  change RuleProofs.smt_value_rel (SmtValue.Set res) (SmtValue.Set mx)
  exact RuleProofs.smt_value_rel_set_of_lookup_eq res mx hResCan hMxCan
    hLeaf hLookup

theorem set_inter_empty_right_rel_of_premise_bool
    (M : SmtModel) (hM : model_wf M)
    (x y T : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hyTrans : RuleProofs.eo_has_smt_translation y)
    (hTypeWf :
      __smtx_type_wf
        (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T)) = true)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq y (mkSetEmpty T)))
    (hFormulaTy : __eo_typeof (mkEq (mkSetInter x y) y) = Term.Bool)
    (hPrem : eo_interprets M (mkEq y (mkSetEmpty T)) true) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkSetInter x y)))
      (__smtx_model_eval M (__eo_to_smt y)) := by
  rcases eo_typeof_set_inter_bool_info (x := x) (y := y) (rhs := y)
      hFormulaTy with
    ⟨U, hxTy, hyTy, _hyTy'⟩
  rcases set_smt_types_of_eo_set_types hxTrans hyTrans hxTy hyTy with
    ⟨hXSmtTyU, hYSmtTyU, _hUNonNone⟩
  have hEmptyTy :
      __smtx_typeof (__eo_to_smt (mkSetEmpty T)) =
        SmtType.Set (__eo_to_smt_type T) :=
    smt_typeof_mkSetEmpty_of_set_type_wf T hTypeWf
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      y (mkSetEmpty T) hPremBool with
    ⟨hYEmptyTy, _hYNonNone⟩
  have hYSmtTyT :
      __smtx_typeof (__eo_to_smt y) = SmtType.Set (__eo_to_smt_type T) :=
    hYEmptyTy.trans hEmptyTy
  have hElemTy : __eo_to_smt_type U = __eo_to_smt_type T := by
    rw [hYSmtTyT] at hYSmtTyU
    injection hYSmtTyU with hEq
    exact hEq.symm
  have hXSmtTyT :
      __smtx_typeof (__eo_to_smt x) = SmtType.Set (__eo_to_smt_type T) := by
    simpa [hElemTy] using hXSmtTyU
  have hSetNonNone :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T) ≠
        SmtType.None :=
    Smtm.type_wf_non_none hTypeWf
  have hTNonNone : __eo_to_smt_type T ≠ SmtType.None :=
    eo_to_smt_type_set_component_non_none T hSetNonNone
  have hYEval := set_eval_eq_empty_of_premise M hM y T hYSmtTyT
    hTNonNone hPrem
  rcases set_value_facts M hM x (__eo_to_smt_type T) hxTrans hXSmtTyT with
    ⟨mx, hXEval, hMxCan, hMxTy, hMxDef⟩
  let empty :=
    SmtMap.default (__eo_to_smt_type T) (SmtValue.Boolean false)
  let acc :=
    SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value mx))
      (SmtValue.Boolean false)
  let res := __smtx_set_op_rec true mx empty acc
  have hEmptyTyMap :
      __smtx_typeof_map_value empty =
        SmtType.Map (__eo_to_smt_type T) SmtType.Bool := by
    dsimp [empty]
    simp [__smtx_typeof_map_value, __smtx_typeof_value]
  have hEmptyCan : __smtx_map_canonical empty = true := by
    dsimp [empty]
    exact set_empty_map_canonical' (__eo_to_smt_type T)
  have hEmptyDef : __smtx_map_get_default empty = SmtValue.Boolean false := by
    dsimp [empty]
    simp [__smtx_map_get_default]
  have hAccTy :
      __smtx_typeof_map_value acc =
        SmtType.Map (__eo_to_smt_type T) SmtType.Bool := by
    dsimp [acc]
    rw [hMxTy]
    simp [__smtx_index_typeof_map, __smtx_typeof_map_value,
      __smtx_typeof_value]
  have hAccCan : __smtx_map_canonical acc = true := by
    dsimp [acc]
    exact set_empty_map_canonical'
      (__smtx_index_typeof_map (__smtx_typeof_map_value mx))
  have hAccDef : __smtx_map_get_default acc = SmtValue.Boolean false := by
    dsimp [acc]
    simp [__smtx_map_get_default]
  have hResCan : __smtx_map_canonical res = true := by
    dsimp [res]
    exact Smtm.mss_op_internal_canonical true hMxCan hAccCan
  have hResTy :
      __smtx_typeof_map_value res =
        SmtType.Map (__eo_to_smt_type T) SmtType.Bool := by
    dsimp [res]
    exact Smtm.mss_op_internal_typed true hMxTy hEmptyTyMap hAccTy
  have hResDef : __smtx_map_get_default res = SmtValue.Boolean false := by
    dsimp [res]
    rw [Smtm.mss_op_internal_get_default]
    exact hAccDef
  have hLeaf : smt_map_default_leaf res = smt_map_default_leaf empty := by
    rw [set_default_leaf hResCan hResTy hResDef]
    dsimp [empty]
    rfl
  have hLookup :
      ∀ v : SmtValue,
        __smtx_map_lookup res v = __smtx_map_lookup empty v := by
    intro v
    dsimp [res, acc]
    rw [set_inter_lookup mx empty (__eo_to_smt_type T) v hMxTy
      hEmptyTyMap hMxCan hMxDef]
    simp [empty, __smtx_map_lookup, native_veq, native_ite,
      SmtEval.native_and]
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M
      (SmtTerm.set_inter (__eo_to_smt x) (__eo_to_smt y)))
    (__smtx_model_eval M (__eo_to_smt y))
  rw [model_eval_inter_eq M (__eo_to_smt x) (__eo_to_smt y), hXEval,
    hYEval]
  change RuleProofs.smt_value_rel (SmtValue.Set res) (SmtValue.Set empty)
  exact RuleProofs.smt_value_rel_set_of_lookup_eq res empty hResCan hEmptyCan
    hLeaf hLookup

theorem set_minus_empty_right_rel_of_premise_bool
    (M : SmtModel) (hM : model_wf M)
    (x y T : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hyTrans : RuleProofs.eo_has_smt_translation y)
    (hTypeWf :
      __smtx_type_wf
        (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T)) = true)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq y (mkSetEmpty T)))
    (hFormulaTy : __eo_typeof (mkEq (mkSetMinus x y) x) = Term.Bool)
    (hPrem : eo_interprets M (mkEq y (mkSetEmpty T)) true) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkSetMinus x y)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  rcases eo_typeof_set_minus_bool_info (x := x) (y := y) (rhs := x)
      hFormulaTy with
    ⟨U, hxTy, hyTy, _hxTy'⟩
  rcases set_smt_types_of_eo_set_types hxTrans hyTrans hxTy hyTy with
    ⟨hXSmtTyU, hYSmtTyU, _hUNonNone⟩
  have hEmptyTy :
      __smtx_typeof (__eo_to_smt (mkSetEmpty T)) =
        SmtType.Set (__eo_to_smt_type T) :=
    smt_typeof_mkSetEmpty_of_set_type_wf T hTypeWf
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      y (mkSetEmpty T) hPremBool with
    ⟨hYEmptyTy, _hYNonNone⟩
  have hYSmtTyT :
      __smtx_typeof (__eo_to_smt y) = SmtType.Set (__eo_to_smt_type T) :=
    hYEmptyTy.trans hEmptyTy
  have hElemTy : __eo_to_smt_type U = __eo_to_smt_type T := by
    rw [hYSmtTyT] at hYSmtTyU
    injection hYSmtTyU with hEq
    exact hEq.symm
  have hXSmtTyT :
      __smtx_typeof (__eo_to_smt x) = SmtType.Set (__eo_to_smt_type T) := by
    simpa [hElemTy] using hXSmtTyU
  have hSetNonNone :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T) ≠
        SmtType.None :=
    Smtm.type_wf_non_none hTypeWf
  have hTNonNone : __eo_to_smt_type T ≠ SmtType.None :=
    eo_to_smt_type_set_component_non_none T hSetNonNone
  have hYEval := set_eval_eq_empty_of_premise M hM y T hYSmtTyT
    hTNonNone hPrem
  rcases set_value_facts M hM x (__eo_to_smt_type T) hxTrans hXSmtTyT with
    ⟨mx, hXEval, hMxCan, hMxTy, hMxDef⟩
  let empty :=
    SmtMap.default (__eo_to_smt_type T) (SmtValue.Boolean false)
  let acc :=
    SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value mx))
      (SmtValue.Boolean false)
  let res := __smtx_set_op_rec false mx empty acc
  have hEmptyTyMap :
      __smtx_typeof_map_value empty =
        SmtType.Map (__eo_to_smt_type T) SmtType.Bool := by
    dsimp [empty]
    simp [__smtx_typeof_map_value, __smtx_typeof_value]
  have hEmptyCan : __smtx_map_canonical empty = true := by
    dsimp [empty]
    exact set_empty_map_canonical' (__eo_to_smt_type T)
  have hEmptyDef : __smtx_map_get_default empty = SmtValue.Boolean false := by
    dsimp [empty]
    simp [__smtx_map_get_default]
  have hAccTy :
      __smtx_typeof_map_value acc =
        SmtType.Map (__eo_to_smt_type T) SmtType.Bool := by
    dsimp [acc]
    rw [hMxTy]
    simp [__smtx_index_typeof_map, __smtx_typeof_map_value,
      __smtx_typeof_value]
  have hAccCan : __smtx_map_canonical acc = true := by
    dsimp [acc]
    exact set_empty_map_canonical'
      (__smtx_index_typeof_map (__smtx_typeof_map_value mx))
  have hAccDef : __smtx_map_get_default acc = SmtValue.Boolean false := by
    dsimp [acc]
    simp [__smtx_map_get_default]
  have hResCan : __smtx_map_canonical res = true := by
    dsimp [res]
    exact Smtm.mss_op_internal_canonical false hMxCan hAccCan
  have hResTy :
      __smtx_typeof_map_value res =
        SmtType.Map (__eo_to_smt_type T) SmtType.Bool := by
    dsimp [res]
    exact Smtm.mss_op_internal_typed false hMxTy hEmptyTyMap hAccTy
  have hResDef : __smtx_map_get_default res = SmtValue.Boolean false := by
    dsimp [res]
    rw [Smtm.mss_op_internal_get_default]
    exact hAccDef
  have hLeaf : smt_map_default_leaf res = smt_map_default_leaf mx := by
    rw [set_default_leaf hResCan hResTy hResDef,
      set_default_leaf hMxCan hMxTy hMxDef]
  have hLookup :
      ∀ v : SmtValue,
        __smtx_map_lookup res v = __smtx_map_lookup mx v := by
    intro v
    dsimp [res, acc]
    rw [set_minus_lookup mx empty (__eo_to_smt_type T) v hMxTy
      hEmptyTyMap hMxCan hMxDef]
    have hFalseTrue :
        native_veq (SmtValue.Boolean false) (SmtValue.Boolean true) =
          false := by
      simp [native_veq]
    rw [show __smtx_map_lookup empty v = SmtValue.Boolean false by
      simp [empty, __smtx_map_lookup], hFalseTrue]
    simpa [native_not, native_and, SmtEval.native_and] using
      set_map_lookup_bool_ite_true_false
        (m := mx) (A := __eo_to_smt_type T) v hMxTy hMxCan hMxDef
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M
      (SmtTerm.set_minus (__eo_to_smt x) (__eo_to_smt y)))
    (__smtx_model_eval M (__eo_to_smt x))
  rw [model_eval_minus_eq M (__eo_to_smt x) (__eo_to_smt y), hXEval,
    hYEval]
  change RuleProofs.smt_value_rel (SmtValue.Set res) (SmtValue.Set mx)
  exact RuleProofs.smt_value_rel_set_of_lookup_eq res mx hResCan hMxCan
    hLeaf hLookup

theorem prog_sets_inter_emp1_info
    (x y ty P : Term)
    (hProg :
      __eo_prog_sets_inter_emp1 x y ty (Proof.pf P) ≠ Term.Stuck) :
    ∃ T x0 T0 : Term,
      ty = Term.Apply (Term.UOp UserOp.Set) T ∧
        P = mkEq x0 (mkSetEmpty T0) ∧
          x0 = x ∧
            T0 = T ∧
              __eo_prog_sets_inter_emp1 x y ty (Proof.pf P) =
                mkEq (mkSetInter x y) x := by
  by_cases hx : x = Term.Stuck
  · subst x
    simp [__eo_prog_sets_inter_emp1] at hProg
  by_cases hy : y = Term.Stuck
  · subst y
    simp [__eo_prog_sets_inter_emp1, hx] at hProg
  cases ty with
  | Apply f T =>
      cases f with
      | UOp op =>
          by_cases hSet : op = UserOp.Set
          · subst op
            cases P with
            | Apply pf rhs =>
                cases pf with
                | Apply pg x0 =>
                    cases pg with
                    | UOp eqOp =>
                        by_cases hEq : eqOp = UserOp.eq
                        · subst eqOp
                          cases rhs with
                          | UOp1 emptyOp setTy =>
                              by_cases hEmpty : emptyOp = UserOp1.set_empty
                              · subst emptyOp
                                cases setTy with
                                | Apply setF T0 =>
                                    cases setF with
                                    | UOp setOp =>
                                        by_cases hSetTy : setOp = UserOp.Set
                                        · subst setOp
                                          let B := mkEq (mkSetInter x y) x
                                          have hReq :
                                              __eo_requires
                                                  (__eo_and (__eo_eq x x0)
                                                    (__eo_eq T T0))
                                                  (Term.Boolean true) B ≠
                                                Term.Stuck := by
                                            simpa [B, __eo_prog_sets_inter_emp1,
                                              hx, hy, mkEq, mkSetInter,
                                              mkSetEmpty] using hProg
                                          have hEqs :
                                              x0 = x ∧ T0 = T :=
                                            RuleProofs.eqs_of_requires_and_eq_true_not_stuck
                                              x T x0 T0 B hReq
                                          have hUnfold :
                                              __eo_prog_sets_inter_emp1 x y
                                                  (Term.Apply
                                                    (Term.UOp UserOp.Set) T)
                                                  (Proof.pf
                                                    (mkEq x0 (mkSetEmpty T0))) =
                                                __eo_requires
                                                  (__eo_and (__eo_eq x x0)
                                                    (__eo_eq T T0))
                                                  (Term.Boolean true) B := by
                                            simp [B, __eo_prog_sets_inter_emp1,
                                              hx, hy, mkEq, mkSetInter,
                                              mkSetEmpty]
                                          refine ⟨T, x0, T0, rfl, rfl,
                                            hEqs.1, hEqs.2, ?_⟩
                                          change
                                            __eo_prog_sets_inter_emp1 x y
                                                (Term.Apply
                                                  (Term.UOp UserOp.Set) T)
                                                (Proof.pf
                                                  (mkEq x0 (mkSetEmpty T0))) =
                                              mkEq (mkSetInter x y) x
                                          rw [hUnfold, SetsEvalOpSupport.req_result hReq]
                                        · exfalso
                                          apply hProg
                                          simp [__eo_prog_sets_inter_emp1, hx,
                                            hy, hSetTy, mkEq, mkSetEmpty]
                                    | _ =>
                                        exfalso
                                        apply hProg
                                        simp [__eo_prog_sets_inter_emp1, hx,
                                          hy, mkEq, mkSetEmpty]
                                | _ =>
                                    exfalso
                                    apply hProg
                                    simp [__eo_prog_sets_inter_emp1, hx, hy,
                                      mkEq, mkSetEmpty]
                              · exfalso
                                apply hProg
                                simp [__eo_prog_sets_inter_emp1, hx, hy,
                                  hEmpty, mkEq, mkSetEmpty]
                          | _ =>
                              exfalso
                              apply hProg
                              simp [__eo_prog_sets_inter_emp1, hx, hy, mkEq,
                                mkSetEmpty]
                        · exfalso
                          apply hProg
                          simp [__eo_prog_sets_inter_emp1, hx, hy, hEq, mkEq,
                            mkSetEmpty]
                    | _ =>
                        exfalso
                        apply hProg
                        simp [__eo_prog_sets_inter_emp1, hx, hy, mkEq,
                          mkSetEmpty]
                | _ =>
                    exfalso
                    apply hProg
                    simp [__eo_prog_sets_inter_emp1, hx, hy, mkEq, mkSetEmpty]
            | _ =>
                exfalso
                apply hProg
                simp [__eo_prog_sets_inter_emp1, hx, hy, mkEq, mkSetEmpty]
          · exfalso
            apply hProg
            simp [__eo_prog_sets_inter_emp1, hx, hy, hSet]
      | _ =>
          exfalso
          apply hProg
          simp [__eo_prog_sets_inter_emp1, hx, hy]
  | _ =>
      exfalso
      apply hProg
      simp [__eo_prog_sets_inter_emp1, hx, hy]

theorem prog_sets_minus_emp1_info
    (x y ty P : Term)
    (hProg :
      __eo_prog_sets_minus_emp1 x y ty (Proof.pf P) ≠ Term.Stuck) :
    ∃ T x0 T0 : Term,
      ty = Term.Apply (Term.UOp UserOp.Set) T ∧
        P = mkEq x0 (mkSetEmpty T0) ∧
          x0 = x ∧
            T0 = T ∧
              __eo_prog_sets_minus_emp1 x y ty (Proof.pf P) =
                mkEq (mkSetMinus x y) x := by
  by_cases hx : x = Term.Stuck
  · subst x
    simp [__eo_prog_sets_minus_emp1] at hProg
  by_cases hy : y = Term.Stuck
  · subst y
    simp [__eo_prog_sets_minus_emp1, hx] at hProg
  cases ty with
  | Apply f T =>
      cases f with
      | UOp op =>
          by_cases hSet : op = UserOp.Set
          · subst op
            cases P with
            | Apply pf rhs =>
                cases pf with
                | Apply pg x0 =>
                    cases pg with
                    | UOp eqOp =>
                        by_cases hEq : eqOp = UserOp.eq
                        · subst eqOp
                          cases rhs with
                          | UOp1 emptyOp setTy =>
                              by_cases hEmpty : emptyOp = UserOp1.set_empty
                              · subst emptyOp
                                cases setTy with
                                | Apply setF T0 =>
                                    cases setF with
                                    | UOp setOp =>
                                        by_cases hSetTy : setOp = UserOp.Set
                                        · subst setOp
                                          let B := mkEq (mkSetMinus x y) x
                                          have hReq :
                                              __eo_requires
                                                  (__eo_and (__eo_eq x x0)
                                                    (__eo_eq T T0))
                                                  (Term.Boolean true) B ≠
                                                Term.Stuck := by
                                            simpa [B, __eo_prog_sets_minus_emp1,
                                              hx, hy, mkEq, mkSetMinus,
                                              mkSetEmpty] using hProg
                                          have hEqs :
                                              x0 = x ∧ T0 = T :=
                                            RuleProofs.eqs_of_requires_and_eq_true_not_stuck
                                              x T x0 T0 B hReq
                                          have hUnfold :
                                              __eo_prog_sets_minus_emp1 x y
                                                  (Term.Apply
                                                    (Term.UOp UserOp.Set) T)
                                                  (Proof.pf
                                                    (mkEq x0 (mkSetEmpty T0))) =
                                                __eo_requires
                                                  (__eo_and (__eo_eq x x0)
                                                    (__eo_eq T T0))
                                                  (Term.Boolean true) B := by
                                            simp [B, __eo_prog_sets_minus_emp1,
                                              hx, hy, mkEq, mkSetMinus,
                                              mkSetEmpty]
                                          refine ⟨T, x0, T0, rfl, rfl,
                                            hEqs.1, hEqs.2, ?_⟩
                                          change
                                            __eo_prog_sets_minus_emp1 x y
                                                (Term.Apply
                                                  (Term.UOp UserOp.Set) T)
                                                (Proof.pf
                                                  (mkEq x0 (mkSetEmpty T0))) =
                                              mkEq (mkSetMinus x y) x
                                          rw [hUnfold, SetsEvalOpSupport.req_result hReq]
                                        · exfalso
                                          apply hProg
                                          simp [__eo_prog_sets_minus_emp1, hx,
                                            hy, hSetTy, mkEq, mkSetEmpty]
                                    | _ =>
                                        exfalso
                                        apply hProg
                                        simp [__eo_prog_sets_minus_emp1, hx,
                                          hy, mkEq, mkSetEmpty]
                                | _ =>
                                    exfalso
                                    apply hProg
                                    simp [__eo_prog_sets_minus_emp1, hx, hy,
                                      mkEq, mkSetEmpty]
                              · exfalso
                                apply hProg
                                simp [__eo_prog_sets_minus_emp1, hx, hy,
                                  hEmpty, mkEq, mkSetEmpty]
                          | _ =>
                              exfalso
                              apply hProg
                              simp [__eo_prog_sets_minus_emp1, hx, hy, mkEq,
                                mkSetEmpty]
                        · exfalso
                          apply hProg
                          simp [__eo_prog_sets_minus_emp1, hx, hy, hEq, mkEq,
                            mkSetEmpty]
                    | _ =>
                        exfalso
                        apply hProg
                        simp [__eo_prog_sets_minus_emp1, hx, hy, mkEq,
                          mkSetEmpty]
                | _ =>
                    exfalso
                    apply hProg
                    simp [__eo_prog_sets_minus_emp1, hx, hy, mkEq, mkSetEmpty]
            | _ =>
                exfalso
                apply hProg
                simp [__eo_prog_sets_minus_emp1, hx, hy, mkEq, mkSetEmpty]
          · exfalso
            apply hProg
            simp [__eo_prog_sets_minus_emp1, hx, hy, hSet]
      | _ =>
          exfalso
          apply hProg
          simp [__eo_prog_sets_minus_emp1, hx, hy]
  | _ =>
      exfalso
      apply hProg
      simp [__eo_prog_sets_minus_emp1, hx, hy]

theorem prog_sets_union_emp2_info
    (x y ty P : Term)
    (hProg :
      __eo_prog_sets_union_emp2 x y ty (Proof.pf P) ≠ Term.Stuck) :
    ∃ T y0 T0 : Term,
      ty = Term.Apply (Term.UOp UserOp.Set) T ∧
        P = mkEq y0 (mkSetEmpty T0) ∧
          y0 = y ∧
            T0 = T ∧
              __eo_prog_sets_union_emp2 x y ty (Proof.pf P) =
                mkEq (mkSetUnion x y) x := by
  by_cases hx : x = Term.Stuck
  · subst x
    simp [__eo_prog_sets_union_emp2] at hProg
  by_cases hy : y = Term.Stuck
  · subst y
    simp [__eo_prog_sets_union_emp2, hx] at hProg
  cases ty with
  | Apply f T =>
      cases f with
      | UOp op =>
          by_cases hSet : op = UserOp.Set
          · subst op
            cases P with
            | Apply pf rhs =>
                cases pf with
                | Apply pg y0 =>
                    cases pg with
                    | UOp eqOp =>
                        by_cases hEq : eqOp = UserOp.eq
                        · subst eqOp
                          cases rhs with
                          | UOp1 emptyOp setTy =>
                              by_cases hEmpty : emptyOp = UserOp1.set_empty
                              · subst emptyOp
                                cases setTy with
                                | Apply setF T0 =>
                                    cases setF with
                                    | UOp setOp =>
                                        by_cases hSetTy : setOp = UserOp.Set
                                        · subst setOp
                                          let B := mkEq (mkSetUnion x y) x
                                          have hReq :
                                              __eo_requires
                                                  (__eo_and (__eo_eq y y0)
                                                    (__eo_eq T T0))
                                                  (Term.Boolean true) B ≠
                                                Term.Stuck := by
                                            simpa [B, __eo_prog_sets_union_emp2,
                                              hx, hy, mkEq, mkSetUnion,
                                              mkSetEmpty] using hProg
                                          have hEqs :
                                              y0 = y ∧ T0 = T :=
                                            RuleProofs.eqs_of_requires_and_eq_true_not_stuck
                                              y T y0 T0 B hReq
                                          have hUnfold :
                                              __eo_prog_sets_union_emp2 x y
                                                  (Term.Apply
                                                    (Term.UOp UserOp.Set) T)
                                                  (Proof.pf
                                                    (mkEq y0 (mkSetEmpty T0))) =
                                                __eo_requires
                                                  (__eo_and (__eo_eq y y0)
                                                    (__eo_eq T T0))
                                                  (Term.Boolean true) B := by
                                            simp [B, __eo_prog_sets_union_emp2,
                                              hx, hy, mkEq, mkSetUnion,
                                              mkSetEmpty]
                                          refine ⟨T, y0, T0, rfl, rfl,
                                            hEqs.1, hEqs.2, ?_⟩
                                          change
                                            __eo_prog_sets_union_emp2 x y
                                                (Term.Apply
                                                  (Term.UOp UserOp.Set) T)
                                                (Proof.pf
                                                  (mkEq y0 (mkSetEmpty T0))) =
                                              mkEq (mkSetUnion x y) x
                                          rw [hUnfold, SetsEvalOpSupport.req_result hReq]
                                        · exfalso
                                          apply hProg
                                          simp [__eo_prog_sets_union_emp2, hx,
                                            hy, hSetTy, mkEq, mkSetEmpty]
                                    | _ =>
                                        exfalso
                                        apply hProg
                                        simp [__eo_prog_sets_union_emp2, hx,
                                          hy, mkEq, mkSetEmpty]
                                | _ =>
                                    exfalso
                                    apply hProg
                                    simp [__eo_prog_sets_union_emp2, hx, hy,
                                      mkEq, mkSetEmpty]
                              · exfalso
                                apply hProg
                                simp [__eo_prog_sets_union_emp2, hx, hy,
                                  hEmpty, mkEq, mkSetEmpty]
                          | _ =>
                              exfalso
                              apply hProg
                              simp [__eo_prog_sets_union_emp2, hx, hy, mkEq,
                                mkSetEmpty]
                        · exfalso
                          apply hProg
                          simp [__eo_prog_sets_union_emp2, hx, hy, hEq, mkEq,
                            mkSetEmpty]
                    | _ =>
                        exfalso
                        apply hProg
                        simp [__eo_prog_sets_union_emp2, hx, hy, mkEq,
                          mkSetEmpty]
                | _ =>
                    exfalso
                    apply hProg
                    simp [__eo_prog_sets_union_emp2, hx, hy, mkEq, mkSetEmpty]
            | _ =>
                exfalso
                apply hProg
                simp [__eo_prog_sets_union_emp2, hx, hy, mkEq, mkSetEmpty]
          · exfalso
            apply hProg
            simp [__eo_prog_sets_union_emp2, hx, hy, hSet]
      | _ =>
          exfalso
          apply hProg
          simp [__eo_prog_sets_union_emp2, hx, hy]
  | _ =>
      exfalso
      apply hProg
      simp [__eo_prog_sets_union_emp2, hx, hy]

theorem prog_sets_inter_emp2_info
    (x y ty P : Term)
    (hProg :
      __eo_prog_sets_inter_emp2 x y ty (Proof.pf P) ≠ Term.Stuck) :
    ∃ T y0 T0 : Term,
      ty = Term.Apply (Term.UOp UserOp.Set) T ∧
        P = mkEq y0 (mkSetEmpty T0) ∧
          y0 = y ∧
            T0 = T ∧
              __eo_prog_sets_inter_emp2 x y ty (Proof.pf P) =
                mkEq (mkSetInter x y) y := by
  by_cases hx : x = Term.Stuck
  · subst x
    simp [__eo_prog_sets_inter_emp2] at hProg
  by_cases hy : y = Term.Stuck
  · subst y
    simp [__eo_prog_sets_inter_emp2, hx] at hProg
  cases ty with
  | Apply f T =>
      cases f with
      | UOp op =>
          by_cases hSet : op = UserOp.Set
          · subst op
            cases P with
            | Apply pf rhs =>
                cases pf with
                | Apply pg y0 =>
                    cases pg with
                    | UOp eqOp =>
                        by_cases hEq : eqOp = UserOp.eq
                        · subst eqOp
                          cases rhs with
                          | UOp1 emptyOp setTy =>
                              by_cases hEmpty : emptyOp = UserOp1.set_empty
                              · subst emptyOp
                                cases setTy with
                                | Apply setF T0 =>
                                    cases setF with
                                    | UOp setOp =>
                                        by_cases hSetTy : setOp = UserOp.Set
                                        · subst setOp
                                          let B := mkEq (mkSetInter x y) y
                                          have hReq :
                                              __eo_requires
                                                  (__eo_and (__eo_eq y y0)
                                                    (__eo_eq T T0))
                                                  (Term.Boolean true) B ≠
                                                Term.Stuck := by
                                            simpa [B, __eo_prog_sets_inter_emp2,
                                              hx, hy, mkEq, mkSetInter,
                                              mkSetEmpty] using hProg
                                          have hEqs :
                                              y0 = y ∧ T0 = T :=
                                            RuleProofs.eqs_of_requires_and_eq_true_not_stuck
                                              y T y0 T0 B hReq
                                          have hUnfold :
                                              __eo_prog_sets_inter_emp2 x y
                                                  (Term.Apply
                                                    (Term.UOp UserOp.Set) T)
                                                  (Proof.pf
                                                    (mkEq y0 (mkSetEmpty T0))) =
                                                __eo_requires
                                                  (__eo_and (__eo_eq y y0)
                                                    (__eo_eq T T0))
                                                  (Term.Boolean true) B := by
                                            simp [B, __eo_prog_sets_inter_emp2,
                                              hx, hy, mkEq, mkSetInter,
                                              mkSetEmpty]
                                          refine ⟨T, y0, T0, rfl, rfl,
                                            hEqs.1, hEqs.2, ?_⟩
                                          change
                                            __eo_prog_sets_inter_emp2 x y
                                                (Term.Apply
                                                  (Term.UOp UserOp.Set) T)
                                                (Proof.pf
                                                  (mkEq y0 (mkSetEmpty T0))) =
                                              mkEq (mkSetInter x y) y
                                          rw [hUnfold, SetsEvalOpSupport.req_result hReq]
                                        · exfalso
                                          apply hProg
                                          simp [__eo_prog_sets_inter_emp2, hx,
                                            hy, hSetTy, mkEq, mkSetEmpty]
                                    | _ =>
                                        exfalso
                                        apply hProg
                                        simp [__eo_prog_sets_inter_emp2, hx,
                                          hy, mkEq, mkSetEmpty]
                                | _ =>
                                    exfalso
                                    apply hProg
                                    simp [__eo_prog_sets_inter_emp2, hx, hy,
                                      mkEq, mkSetEmpty]
                              · exfalso
                                apply hProg
                                simp [__eo_prog_sets_inter_emp2, hx, hy,
                                  hEmpty, mkEq, mkSetEmpty]
                          | _ =>
                              exfalso
                              apply hProg
                              simp [__eo_prog_sets_inter_emp2, hx, hy, mkEq,
                                mkSetEmpty]
                        · exfalso
                          apply hProg
                          simp [__eo_prog_sets_inter_emp2, hx, hy, hEq, mkEq,
                            mkSetEmpty]
                    | _ =>
                        exfalso
                        apply hProg
                        simp [__eo_prog_sets_inter_emp2, hx, hy, mkEq,
                          mkSetEmpty]
                | _ =>
                    exfalso
                    apply hProg
                    simp [__eo_prog_sets_inter_emp2, hx, hy, mkEq, mkSetEmpty]
            | _ =>
                exfalso
                apply hProg
                simp [__eo_prog_sets_inter_emp2, hx, hy, mkEq, mkSetEmpty]
          · exfalso
            apply hProg
            simp [__eo_prog_sets_inter_emp2, hx, hy, hSet]
      | _ =>
          exfalso
          apply hProg
          simp [__eo_prog_sets_inter_emp2, hx, hy]
  | _ =>
      exfalso
      apply hProg
      simp [__eo_prog_sets_inter_emp2, hx, hy]

theorem prog_sets_minus_emp2_info
    (x y ty P : Term)
    (hProg :
      __eo_prog_sets_minus_emp2 x y ty (Proof.pf P) ≠ Term.Stuck) :
    ∃ T y0 T0 : Term,
      ty = Term.Apply (Term.UOp UserOp.Set) T ∧
        P = mkEq y0 (mkSetEmpty T0) ∧
          y0 = y ∧
            T0 = T ∧
              __eo_prog_sets_minus_emp2 x y ty (Proof.pf P) =
                mkEq (mkSetMinus x y) x := by
  by_cases hx : x = Term.Stuck
  · subst x
    simp [__eo_prog_sets_minus_emp2] at hProg
  by_cases hy : y = Term.Stuck
  · subst y
    simp [__eo_prog_sets_minus_emp2, hx] at hProg
  cases ty with
  | Apply f T =>
      cases f with
      | UOp op =>
          by_cases hSet : op = UserOp.Set
          · subst op
            cases P with
            | Apply pf rhs =>
                cases pf with
                | Apply pg y0 =>
                    cases pg with
                    | UOp eqOp =>
                        by_cases hEq : eqOp = UserOp.eq
                        · subst eqOp
                          cases rhs with
                          | UOp1 emptyOp setTy =>
                              by_cases hEmpty : emptyOp = UserOp1.set_empty
                              · subst emptyOp
                                cases setTy with
                                | Apply setF T0 =>
                                    cases setF with
                                    | UOp setOp =>
                                        by_cases hSetTy : setOp = UserOp.Set
                                        · subst setOp
                                          let B := mkEq (mkSetMinus x y) x
                                          have hReq :
                                              __eo_requires
                                                  (__eo_and (__eo_eq y y0)
                                                    (__eo_eq T T0))
                                                  (Term.Boolean true) B ≠
                                                Term.Stuck := by
                                            simpa [B, __eo_prog_sets_minus_emp2,
                                              hx, hy, mkEq, mkSetMinus,
                                              mkSetEmpty] using hProg
                                          have hEqs :
                                              y0 = y ∧ T0 = T :=
                                            RuleProofs.eqs_of_requires_and_eq_true_not_stuck
                                              y T y0 T0 B hReq
                                          have hUnfold :
                                              __eo_prog_sets_minus_emp2 x y
                                                  (Term.Apply
                                                    (Term.UOp UserOp.Set) T)
                                                  (Proof.pf
                                                    (mkEq y0 (mkSetEmpty T0))) =
                                                __eo_requires
                                                  (__eo_and (__eo_eq y y0)
                                                    (__eo_eq T T0))
                                                  (Term.Boolean true) B := by
                                            simp [B, __eo_prog_sets_minus_emp2,
                                              hx, hy, mkEq, mkSetMinus,
                                              mkSetEmpty]
                                          refine ⟨T, y0, T0, rfl, rfl,
                                            hEqs.1, hEqs.2, ?_⟩
                                          change
                                            __eo_prog_sets_minus_emp2 x y
                                                (Term.Apply
                                                  (Term.UOp UserOp.Set) T)
                                                (Proof.pf
                                                  (mkEq y0 (mkSetEmpty T0))) =
                                              mkEq (mkSetMinus x y) x
                                          rw [hUnfold, SetsEvalOpSupport.req_result hReq]
                                        · exfalso
                                          apply hProg
                                          simp [__eo_prog_sets_minus_emp2, hx,
                                            hy, hSetTy, mkEq, mkSetEmpty]
                                    | _ =>
                                        exfalso
                                        apply hProg
                                        simp [__eo_prog_sets_minus_emp2, hx,
                                          hy, mkEq, mkSetEmpty]
                                | _ =>
                                    exfalso
                                    apply hProg
                                    simp [__eo_prog_sets_minus_emp2, hx, hy,
                                      mkEq, mkSetEmpty]
                              · exfalso
                                apply hProg
                                simp [__eo_prog_sets_minus_emp2, hx, hy,
                                  hEmpty, mkEq, mkSetEmpty]
                          | _ =>
                              exfalso
                              apply hProg
                              simp [__eo_prog_sets_minus_emp2, hx, hy, mkEq,
                                mkSetEmpty]
                        · exfalso
                          apply hProg
                          simp [__eo_prog_sets_minus_emp2, hx, hy, hEq, mkEq,
                            mkSetEmpty]
                    | _ =>
                        exfalso
                        apply hProg
                        simp [__eo_prog_sets_minus_emp2, hx, hy, mkEq,
                          mkSetEmpty]
                | _ =>
                    exfalso
                    apply hProg
                    simp [__eo_prog_sets_minus_emp2, hx, hy, mkEq, mkSetEmpty]
            | _ =>
                exfalso
                apply hProg
                simp [__eo_prog_sets_minus_emp2, hx, hy, mkEq, mkSetEmpty]
          · exfalso
            apply hProg
            simp [__eo_prog_sets_minus_emp2, hx, hy, hSet]
      | _ =>
          exfalso
          apply hProg
          simp [__eo_prog_sets_minus_emp2, hx, hy]
  | _ =>
      exfalso
      apply hProg
      simp [__eo_prog_sets_minus_emp2, hx, hy]

theorem typed_set_minus_self_eq_empty
    (x T : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hTypeWf :
      __smtx_type_wf
        (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T)) = true)
    (hTy : __eo_typeof (mkEq (mkSetMinus x x) (mkSetEmpty T)) = Term.Bool) :
    RuleProofs.eo_has_bool_type (mkEq (mkSetMinus x x) (mkSetEmpty T)) := by
  have hxTy : __eo_typeof x = Term.Apply (Term.UOp UserOp.Set) T :=
    eo_typeof_set_minus_self_bool_info hTy
  rcases set_smt_types_of_eo_set_types hxTrans hxTrans hxTy hxTy with
    ⟨hXSmtTy, _hXSmtTy', _hTNonNone⟩
  have hMinusTy :
      __smtx_typeof (__eo_to_smt (mkSetMinus x x)) =
        SmtType.Set (__eo_to_smt_type T) := by
    change
      __smtx_typeof (SmtTerm.set_minus (__eo_to_smt x) (__eo_to_smt x)) =
        SmtType.Set (__eo_to_smt_type T)
    rw [typeof_set_minus_eq]
    simp [__smtx_typeof_sets_op_2, hXSmtTy, native_ite, native_Teq]
  have hEmptyTy :
      __smtx_typeof (__eo_to_smt (mkSetEmpty T)) =
        SmtType.Set (__eo_to_smt_type T) :=
    smt_typeof_mkSetEmpty_of_set_type_wf T hTypeWf
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (mkSetMinus x x) (mkSetEmpty T)
    (by rw [hMinusTy, hEmptyTy])
    (by rw [hMinusTy]; simp)

theorem set_minus_self_lookup_false
    (m : SmtMap) (A : SmtType) (v : SmtValue)
    (hmTy : __smtx_typeof_map_value m = SmtType.Map A SmtType.Bool)
    (hmCan : __smtx_map_canonical m = true)
    (hmDef : __smtx_map_get_default m = SmtValue.Boolean false) :
    __smtx_map_lookup
        (__smtx_set_op_rec false m m
          (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m))
            (SmtValue.Boolean false))) v =
      SmtValue.Boolean false := by
  rw [set_minus_lookup m m A v hmTy hmTy hmCan hmDef]
  cases hLookup :
      native_veq (__smtx_map_lookup m v) (SmtValue.Boolean true) <;>
    simp [hLookup, native_ite, native_not, SmtEval.native_and]

theorem set_minus_self_rel
    (M : SmtModel) (hM : model_wf M)
    (x T : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hTy : __eo_typeof (mkEq (mkSetMinus x x) (mkSetEmpty T)) = Term.Bool) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkSetMinus x x)))
      (__smtx_model_eval M (__eo_to_smt (mkSetEmpty T))) := by
  have hxTy : __eo_typeof x = Term.Apply (Term.UOp UserOp.Set) T :=
    eo_typeof_set_minus_self_bool_info hTy
  rcases set_smt_types_of_eo_set_types hxTrans hxTrans hxTy hxTy with
    ⟨hXSmtTy, _hXSmtTy', hTNonNone⟩
  rcases set_value_facts M hM x (__eo_to_smt_type T) hxTrans hXSmtTy with
    ⟨m, hXEval, hmCan, hmTy, hmDef⟩
  have hEmptyEval := model_eval_set_empty M T hTNonNone
  let acc :=
    SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m))
      (SmtValue.Boolean false)
  let res := __smtx_set_op_rec false m m acc
  let empty := SmtMap.default (__eo_to_smt_type T) (SmtValue.Boolean false)
  have hAccTy :
      __smtx_typeof_map_value acc =
        SmtType.Map (__eo_to_smt_type T) SmtType.Bool := by
    dsimp [acc]
    rw [hmTy]
    simp [__smtx_index_typeof_map, __smtx_typeof_map_value,
      __smtx_typeof_value]
  have hAccCan : __smtx_map_canonical acc = true := by
    dsimp [acc]
    exact set_empty_map_canonical (__smtx_index_typeof_map (__smtx_typeof_map_value m))
  have hResCan : __smtx_map_canonical res = true := by
    dsimp [res]
    exact Smtm.mss_op_internal_canonical false hmCan hAccCan
  have hResTy :
      __smtx_typeof_map_value res =
        SmtType.Map (__eo_to_smt_type T) SmtType.Bool := by
    dsimp [res]
    exact Smtm.mss_op_internal_typed false hmTy hmTy hAccTy
  have hResDef : __smtx_map_get_default res = SmtValue.Boolean false := by
    dsimp [res, acc]
    rw [Smtm.mss_op_internal_get_default]
    simp [__smtx_map_get_default]
  have hEmptyCan : __smtx_map_canonical empty = true := by
    dsimp [empty]
    exact set_empty_map_canonical (__eo_to_smt_type T)
  have hLeaf :
      Smtm.smt_map_default_leaf res = Smtm.smt_map_default_leaf empty := by
    rw [set_default_leaf hResCan hResTy hResDef]
    dsimp [empty]
    rw [set_empty_map_default_leaf]
  have hLookup :
      ∀ v : SmtValue,
        __smtx_map_lookup res v = __smtx_map_lookup empty v := by
    intro v
    dsimp [res, empty, acc]
    rw [set_minus_self_lookup_false m (__eo_to_smt_type T) v hmTy hmCan hmDef]
    simp [__smtx_map_lookup]
  change
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (SmtTerm.set_minus (__eo_to_smt x) (__eo_to_smt x)))
      (__smtx_model_eval M (__eo_to_smt (mkSetEmpty T)))
  rw [model_eval_minus_eq M (__eo_to_smt x) (__eo_to_smt x), hXEval,
    hEmptyEval]
  change RuleProofs.smt_value_rel (SmtValue.Set res) (SmtValue.Set empty)
  exact RuleProofs.smt_value_rel_set_of_lookup_eq res empty hResCan hEmptyCan
    hLeaf hLookup

theorem facts_set_minus_self_eq_empty
    (M : SmtModel) (hM : model_wf M)
    (x T : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hTypeWf :
      __smtx_type_wf
        (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T)) = true)
    (hTy : __eo_typeof (mkEq (mkSetMinus x x) (mkSetEmpty T)) = Term.Bool) :
    eo_interprets M (mkEq (mkSetMinus x x) (mkSetEmpty T)) true := by
  exact RuleProofs.eo_interprets_eq_of_rel M (mkSetMinus x x) (mkSetEmpty T)
    (typed_set_minus_self_eq_empty x T hxTrans hTypeWf hTy)
    (set_minus_self_rel M hM x T hxTrans hTy)

/-- Bridge lemma: a Set type is well-formed precisely when its element type's
    well-formedness component holds (the Set inhabitation check is
    unconditional). -/
theorem type_wf_set_of_component (A : SmtType)
    (h : __smtx_type_wf_component A = true) :
    __smtx_type_wf (SmtType.Set A) = true := by
  simp [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
    native_inhabited_type_set, SmtEval.native_and] at h ⊢
  exact h

/-- Looking up element `i` in the canonical singleton map `{v ↦ true}` over a
    default-`false` map yields `true` exactly when `i = v`. -/
private theorem singleton_map_lookup (v i : SmtValue) (A : SmtType) :
    __smtx_map_lookup
        (SmtMap.cons v (SmtValue.Boolean true)
          (SmtMap.default A (SmtValue.Boolean false))) i =
      native_ite (native_veq v i) (SmtValue.Boolean true)
        (SmtValue.Boolean false) := by
  simp [__smtx_map_lookup]

/-- The SMT `map_diff` of a canonical singleton set `{v}` and the empty set is
    exactly the element `v`.  This is the semantic core of `sets_choose_singleton`:
    the witness `i` distinguishing the two maps is uniquely `v`. -/
theorem map_diff_singleton_empty_eq
    (v : SmtValue) (A : SmtType)
    (hvTy : __smtx_typeof_value v = A)
    (hvCan : __smtx_value_canonical v = true) :
    native_eval_map_diff
        (SmtMap.cons v (SmtValue.Boolean true)
          (SmtMap.default A (SmtValue.Boolean false)))
        (SmtMap.default A (SmtValue.Boolean false)) = v := by
  classical
  -- the distinguishing predicate holds exactly at `i = v`
  have hPredIffV :
      ∀ i : SmtValue,
        (__smtx_typeof_value i = A ∧
          __smtx_value_canonical i = true ∧
            native_veq
              (__smtx_map_lookup
                (SmtMap.cons v (SmtValue.Boolean true)
                  (SmtMap.default A (SmtValue.Boolean false))) i)
              (__smtx_map_lookup
                (SmtMap.default A (SmtValue.Boolean false)) i) =
              false) ↔ i = v := by
    intro i
    constructor
    · rintro ⟨_hiTy, _hiCan, hVeq⟩
      rw [singleton_map_lookup v i A, __smtx_map_lookup] at hVeq
      by_cases hvi : native_veq v i = true
      · exact (Smtm.eq_of_native_veq_true hvi).symm
      · have hvif : native_veq v i = false := by
          cases hb : native_veq v i <;> simp [hb] at hvi ⊢
        rw [hvif] at hVeq
        simp [native_ite, native_veq] at hVeq
    · intro hiv
      subst hiv
      refine ⟨hvTy, hvCan, ?_⟩
      rw [singleton_map_lookup i i A, __smtx_map_lookup]
      simp [native_ite, native_veq]
  have hTypm1 :
      __smtx_typeof_map_value
          (SmtMap.cons v (SmtValue.Boolean true)
            (SmtMap.default A (SmtValue.Boolean false))) =
        SmtType.Map A SmtType.Bool := by
    simp [__smtx_typeof_map_value, __smtx_typeof_value, hvTy,
      native_ite, native_Teq]
  have hTypm2 :
      __smtx_typeof_map_value (SmtMap.default A (SmtValue.Boolean false)) =
        SmtType.Map A SmtType.Bool := by
    simp [__smtx_typeof_map_value, __smtx_typeof_value]
  -- unfold the (noncomputable) map_diff evaluator
  have hDiff :
      ∃ i : SmtValue,
        __smtx_typeof_value i = A ∧
          __smtx_value_canonical i = true ∧
            native_veq
              (__smtx_map_lookup
                (SmtMap.cons v (SmtValue.Boolean true)
                  (SmtMap.default A (SmtValue.Boolean false))) i)
              (__smtx_map_lookup
                (SmtMap.default A (SmtValue.Boolean false)) i) = false :=
    ⟨v, (hPredIffV v).mpr rfl⟩
  have hChoose : Classical.choose hDiff = v :=
    (hPredIffV (Classical.choose hDiff)).mp (Classical.choose_spec hDiff)
  rw [hTypm1, hTypm2]
  simp only [native_ite, native_Teq, SmtEval.native_and, decide_true,
    Bool.and_self, if_true]
  rw [dif_pos hDiff, hChoose]

end SetsBasicRewritesSupport
