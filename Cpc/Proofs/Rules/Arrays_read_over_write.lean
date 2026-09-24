module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.Canonical.Maps
import all Cpc.Proofs.Canonical.Maps

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_to_smt_eq_eq (x y : Term) :
    __eo_to_smt (Term.Apply (Term.Apply Term.eq x) y) =
      SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y) := by
  rfl

private theorem eo_to_smt_select_eq (a i : Term) :
    __eo_to_smt (Term.Apply (Term.Apply Term.select a) i) =
      SmtTerm.select (__eo_to_smt a) (__eo_to_smt i) := by
  rfl

private theorem eo_to_smt_store_eq (a i e : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e) =
      SmtTerm.store (__eo_to_smt a) (__eo_to_smt i) (__eo_to_smt e) := by
  rfl

private theorem model_eval_eq_false_of_eo_eq_false
    (M : SmtModel) (x y : Term) :
    eo_interprets M (Term.Apply (Term.Apply Term.eq x) y) false ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) = SmtValue.Boolean false := by
  intro h
  rw [RuleProofs.eo_interprets_iff_smt_interprets, eo_to_smt_eq_eq] at h
  cases h with
  | intro_false _ hEval =>
      rw [smtx_eval_eq_term_eq] at hEval
      exact hEval

private theorem model_eval_eq_false_of_not_eq_true
    (M : SmtModel) (x y : Term) :
    eo_interprets M (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq x) y)) true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) = SmtValue.Boolean false := by
  intro h
  exact model_eval_eq_false_of_eo_eq_false M x y
    (RuleProofs.eo_interprets_not_true_implies_false M _ h)

private theorem native_veq_false_of_model_eval_eq_false
    {v1 v2 : SmtValue}
    (h : __smtx_model_eval_eq v1 v2 = SmtValue.Boolean false) :
    native_veq v1 v2 = false := by
  by_cases hEq : native_veq v1 v2 = false
  · exact hEq
  · have hEqTrue : native_veq v1 v2 = true := by
      cases hV : native_veq v1 v2 with
      | false =>
          exfalso
          exact hEq hV
      | true =>
          rfl
    have hv : v1 = v2 := by
      simpa [native_veq] using hEqTrue
    subst v2
    rw [RuleProofs.smtx_model_eval_eq_refl] at h
    cases h

private theorem map_lookup_update_aux_other_any :
    ∀ (m : SmtMap) {i j e : SmtValue},
      native_veq i j = false ->
        __smtx_map_lookup
          (__smtx_map_update_aux (__smtx_map_get_default m) m i e) j =
            __smtx_map_lookup m j
  | SmtMap.default T d, i, j, e, hij => by
      exact Smtm.map_lookup_update_aux_no_default_other
        (__smtx_map_get_default (SmtMap.default T d)) (SmtMap.default T d)
        (i := i) (j := j) (e := e) hij
  | SmtMap.cons k v m, i, j, e, hij => by
      cases hki : native_veq k i
      · cases hcmp : native_vcmp k i
        · have hRec :
              __smtx_map_lookup
                  (__smtx_map_update_aux (__smtx_map_get_default m) m i e) j =
                __smtx_map_lookup m j :=
            map_lookup_update_aux_other_any m (i := i) (j := j) (e := e) hij
          cases hkj : native_veq k j <;>
            simp [__smtx_map_update_aux, __smtx_map_lookup, native_ite,
              hki, hcmp, hkj, hRec, __smtx_map_get_default]
        · simpa [__smtx_map_update_aux, native_ite, hki, hcmp] using
            Smtm.map_lookup_update_aux_no_default_other
              (__smtx_map_get_default (SmtMap.cons k v m)) (SmtMap.cons k v m)
              (i := i) (j := j) (e := e) hij
      · have hkiEq : k = i := Smtm.eq_of_native_veq_true hki
        subst i
        have hkj : native_veq k j = false := hij
        have hNoDefault :
            __smtx_map_lookup
                (__smtx_map_update_aux_no_default (__smtx_map_get_default m) m k e) j =
              __smtx_map_lookup m j :=
          Smtm.map_lookup_update_aux_no_default_other
            (__smtx_map_get_default m) m (i := k) (j := j) (e := e) hkj
        simpa [__smtx_map_update_aux, __smtx_map_lookup, native_ite,
          hki, hkj, __smtx_map_get_default] using hNoDefault

private theorem smt_value_rel_select_store_other_of_native_veq_false
    (v i j e : SmtValue)
    (hij : native_veq i j = false) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval_select (__smtx_model_eval_store v i e) j)
      (__smtx_model_eval_select v j) := by
  cases v <;>
    try
      simpa [__smtx_model_eval_select, __smtx_model_eval_store,
        __smtx_map_select, __smtx_map_store] using
        RuleProofs.smt_value_rel_refl SmtValue.NotValue
  · have hLookup :
        __smtx_model_eval_select
            (__smtx_model_eval_store (SmtValue.Map ‹SmtMap›) i e) j =
          __smtx_model_eval_select (SmtValue.Map ‹SmtMap›) j := by
      simpa [__smtx_model_eval_select, __smtx_model_eval_store,
        __smtx_map_select, __smtx_map_store] using
        map_lookup_update_aux_other_any ‹SmtMap› (i := i) (j := j) (e := e) hij
    rw [hLookup]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval_select (SmtValue.Map ‹SmtMap›) j)
  · have hLookup :
        __smtx_model_eval_select
            (__smtx_model_eval_store (SmtValue.Set ‹SmtMap›) i e) j =
          __smtx_model_eval_select (SmtValue.Set ‹SmtMap›) j := by
      simpa [__smtx_model_eval_select, __smtx_model_eval_store,
        __smtx_map_select, __smtx_map_store] using
        map_lookup_update_aux_other_any ‹SmtMap› (i := i) (j := j) (e := e) hij
    rw [hLookup]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval_select (SmtValue.Set ‹SmtMap›) j)

private theorem eq_of_eo_eq_true (x y : Term)
    (h : __eo_eq x y = Term.Boolean true) :
    y = x := by
  by_cases hx : x = Term.Stuck
  · subst x
    simp [__eo_eq] at h
  · by_cases hy : y = Term.Stuck
    · subst y
      simp [__eo_eq] at h
    · have hDec : native_teq y x = true := by
        simpa [__eo_eq, hx, hy] using h
      simpa [native_teq] using hDec

private theorem eqs_of_requires_and_eq_true_not_stuck (x1 y1 x2 y2 B : Term) :
    __eo_requires (__eo_and (__eo_eq x1 x2) (__eo_eq y1 y2))
      (Term.Boolean true) B ≠ Term.Stuck ->
    x2 = x1 ∧ y2 = y1 := by
  intro hProg
  have hProg' := hProg
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not] at hProg'
  have hAnd : __eo_and (__eo_eq x1 x2) (__eo_eq y1 y2) = Term.Boolean true := hProg'.1
  have hBoth :
      __eo_eq x1 x2 = Term.Boolean true ∧ __eo_eq y1 y2 = Term.Boolean true := by
    have eq_stuck_or_bool :
        ∀ a b : Term, __eo_eq a b = Term.Stuck ∨
          ∃ c : native_Bool, __eo_eq a b = Term.Boolean c := by
      intro a b
      by_cases ha : a = Term.Stuck
      · subst a
        exact Or.inl (by simp [__eo_eq])
      · by_cases hb : b = Term.Stuck
        · subst b
          exact Or.inl (by simp [__eo_eq])
        · exact Or.inr ⟨native_teq b a, by simp [__eo_eq]⟩
    rcases eq_stuck_or_bool x1 x2 with hX | ⟨b1, hX⟩
    · simp [__eo_and, hX] at hAnd
    rcases eq_stuck_or_bool y1 y2 with hY | ⟨b2, hY⟩
    · simp [__eo_and, hX, hY] at hAnd
    cases b1 <;> cases b2 <;> simp [__eo_and, hX, hY, native_and] at hAnd ⊢
  exact ⟨eq_of_eo_eq_true x1 x2 hBoth.1, eq_of_eo_eq_true y1 y2 hBoth.2⟩

private theorem smt_type_ne_none_of_wf_rec
    {T : SmtType}
    (h : __smtx_type_wf_rec T = true) :
    T ≠ SmtType.None := by
  intro hNone
  subst T
  simp [__smtx_type_wf_rec] at h

private theorem prog_arrays_read_over_write_eq
    (a i e j i2 j2 : Term) :
    __eo_prog_arrays_read_over_write
      (Term.Apply
        (Term.Apply Term.select
          (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) j)
      (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq i2) j2))) =
      __eo_requires (__eo_and (__eo_eq i i2) (__eo_eq j j2)) (Term.Boolean true)
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply
              (Term.Apply Term.select
                (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) j))
          (Term.Apply (Term.Apply Term.select a) j)) := by
  rfl

private theorem shape_of_prog_arrays_read_over_write_not_stuck
    (x p : Term)
    (h : __eo_prog_arrays_read_over_write x (Proof.pf p) ≠ Term.Stuck) :
    ∃ a i e j i2 j2 : Term,
      x =
        Term.Apply
          (Term.Apply Term.select
            (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) j ∧
      p = Term.Apply Term.not (Term.Apply (Term.Apply Term.eq i2) j2) := by
  cases x with
  | Apply f j =>
      cases f with
      | Apply g storeTerm =>
          cases g with
          | UOp op =>
              cases op <;> try (simp [__eo_prog_arrays_read_over_write] at h)
              case select =>
                cases storeTerm with
                | Apply fStoreE e =>
                    cases fStoreE with
                    | Apply fStoreI i =>
                        cases fStoreI with
                        | Apply storeOp a =>
                            cases storeOp with
                            | UOp op =>
                                cases op <;> try (simp at h)
                                case store =>
                                  cases p with
                                  | Apply pNot pArg =>
                                      cases pNot with
                                      | UOp opNot =>
                                          cases opNot <;>
                                            try (simp at h)
                                          case not =>
                                            cases pArg with
                                            | Apply pEqR j2 =>
                                                cases pEqR with
                                                | Apply pEqL i2 =>
                                                    cases pEqL with
                                                    | UOp opEq =>
                                                        cases opEq <;>
                                                          try (simp at h)
                                                        case eq =>
                                                          exact ⟨a, i, e, j, i2, j2, rfl, rfl⟩
                                                    | _ =>
                                                        simp at h
                                                | _ =>
                                                    simp at h
                                            | _ =>
                                                simp at h
                                      | _ =>
                                          simp at h
                                  | _ =>
                                      simp at h
                            | _ =>
                                simp at h
                        | _ =>
                            simp at h
                    | _ =>
                        simp at h
                | _ =>
                    simp at h
          | _ =>
              simp [__eo_prog_arrays_read_over_write] at h
      | _ =>
          simp [__eo_prog_arrays_read_over_write] at h
  | _ =>
      simp [__eo_prog_arrays_read_over_write] at h

private theorem eo_eq_self_true_of_ne_stuck (x : Term)
    (hx : x ≠ Term.Stuck) :
    __eo_eq x x = Term.Boolean true := by
  cases x <;> simp [__eo_eq, native_teq] at hx ⊢

private theorem requires_and_eq_self_true_body
    (i j body : Term)
    (hINotStuck : i ≠ Term.Stuck)
    (hJNotStuck : j ≠ Term.Stuck) :
    __eo_requires (__eo_and (__eo_eq i i) (__eo_eq j j))
      (Term.Boolean true) body = body := by
  simp [__eo_requires, __eo_and, eo_eq_self_true_of_ne_stuck i hINotStuck,
    eo_eq_self_true_of_ne_stuck j hJNotStuck, native_ite, native_teq,
    native_not, SmtEval.native_not, SmtEval.native_and]

private theorem smt_types_of_select_store_arg
    (a i e j : Term)
    (hArgTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply Term.select
            (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) j)) :
    ∃ A B : SmtType,
      __smtx_typeof (__eo_to_smt a) = SmtType.Map A B ∧
        __smtx_typeof (__eo_to_smt i) = A ∧
        __smtx_typeof (__eo_to_smt e) = B ∧
        __smtx_typeof (__eo_to_smt j) = A ∧
        __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply Term.select
                (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) j)) = B ∧
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.select a) j)) = B ∧
        A ≠ SmtType.None ∧
        B ≠ SmtType.None ∧
        RuleProofs.eo_has_smt_translation a ∧
        RuleProofs.eo_has_smt_translation i ∧
        RuleProofs.eo_has_smt_translation e ∧
        RuleProofs.eo_has_smt_translation j := by
  let storeTerm := Term.Apply (Term.Apply (Term.Apply Term.store a) i) e
  let selectTerm := Term.Apply (Term.Apply Term.select storeTerm) j
  have hSelectNN :
      term_has_non_none_type
        (SmtTerm.select (SmtTerm.store (__eo_to_smt a) (__eo_to_smt i) (__eo_to_smt e))
          (__eo_to_smt j)) := by
    simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type,
      eo_to_smt_select_eq, eo_to_smt_store_eq,
      storeTerm, selectTerm] using hArgTrans
  rcases Smtm.select_args_of_non_none hSelectNN with ⟨A, B, hStoreTy, hJTy⟩
  have hStoreNN :
      term_has_non_none_type
        (SmtTerm.store (__eo_to_smt a) (__eo_to_smt i) (__eo_to_smt e)) := by
    unfold term_has_non_none_type
    rw [hStoreTy]
    simp
  rcases Smtm.store_args_of_non_none hStoreNN with ⟨A', B', hATy, hITy, hETy⟩
  have hStoreTy' :
      SmtType.Map A' B' = SmtType.Map A B := by
    rw [Smtm.typeof_store_eq] at hStoreTy
    simpa [Smtm.typeof_store_eq, __smtx_typeof_store, native_ite, native_Teq,
      hATy, hITy, hETy] using hStoreTy
  cases hStoreTy'
  have hSelectTy :
      __smtx_typeof
          (SmtTerm.select
            (SmtTerm.store (__eo_to_smt a) (__eo_to_smt i) (__eo_to_smt e))
            (__eo_to_smt j)) = B := by
    rw [Smtm.typeof_select_eq]
    simp [__smtx_typeof_select, native_ite, native_Teq, hStoreTy, hJTy]
  have hRhsTy :
      __smtx_typeof (SmtTerm.select (__eo_to_smt a) (__eo_to_smt j)) = B := by
    rw [Smtm.typeof_select_eq]
    simp [__smtx_typeof_select, native_ite, native_Teq, hATy, hJTy]
  have hBNonNone : B ≠ SmtType.None := by
    unfold term_has_non_none_type at hSelectNN
    rw [hSelectTy] at hSelectNN
    exact hSelectNN
  have hARec :
      __smtx_type_wf_rec A = true :=
    (Smtm.smt_map_components_wf_rec_of_non_none_type
      (__eo_to_smt a) A B hATy).1
  have hANonNone : A ≠ SmtType.None :=
    smt_type_ne_none_of_wf_rec hARec
  have hATrans : RuleProofs.eo_has_smt_translation a := by
    simp [RuleProofs.eo_has_smt_translation, hATy]
  have hITrans : RuleProofs.eo_has_smt_translation i := by
    simpa [RuleProofs.eo_has_smt_translation, hITy] using hANonNone
  have hETrans : RuleProofs.eo_has_smt_translation e := by
    simpa [RuleProofs.eo_has_smt_translation, hETy] using hBNonNone
  have hJTrans : RuleProofs.eo_has_smt_translation j := by
    simpa [RuleProofs.eo_has_smt_translation, hJTy] using hANonNone
  exact ⟨A, B, hATy, hITy, hETy, hJTy, by
    simpa [eo_to_smt_select_eq, eo_to_smt_store_eq,
      storeTerm, selectTerm] using hSelectTy, by
    simpa [eo_to_smt_select_eq] using hRhsTy,
    hANonNone, hBNonNone, hATrans, hITrans, hETrans, hJTrans⟩

private theorem typed___eo_prog_arrays_read_over_write_impl
    (a i e j i2 j2 : Term) :
  RuleProofs.eo_has_smt_translation
    (Term.Apply
      (Term.Apply Term.select
        (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) j) ->
  __eo_typeof
      (__eo_prog_arrays_read_over_write
        (Term.Apply
          (Term.Apply Term.select
            (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) j)
        (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq i2) j2)))) =
    Term.Bool ->
  RuleProofs.eo_has_bool_type
    (__eo_prog_arrays_read_over_write
      (Term.Apply
        (Term.Apply Term.select
          (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) j)
      (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq i2) j2)))) := by
  intro hArgTrans hResultTy
  let lhs :=
    Term.Apply
      (Term.Apply Term.select
        (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) j
  let rhs := Term.Apply (Term.Apply Term.select a) j
  let body := Term.Apply (Term.Apply Term.eq lhs) rhs
  have hProg :
      __eo_prog_arrays_read_over_write
          (Term.Apply
            (Term.Apply Term.select
              (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) j)
          (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq i2) j2))) ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  rw [prog_arrays_read_over_write_eq a i e j i2 j2] at hProg hResultTy
  have hAlign :
      i2 = i ∧ j2 = j :=
    eqs_of_requires_and_eq_true_not_stuck i j i2 j2 body hProg
  have hi2 : i2 = i := hAlign.1
  have hj2 : j2 = j := hAlign.2
  subst i2
  subst j2
  have hINotStuck : i ≠ Term.Stuck := by
    intro hi
    subst i
    simp [__eo_requires, __eo_and, __eo_eq, native_ite,
      native_teq] at hProg
  have hJNotStuck : j ≠ Term.Stuck := by
    intro hj
    subst j
    simp [__eo_requires, __eo_and, __eo_eq, native_ite,
      native_teq] at hProg
  rcases smt_types_of_select_store_arg a i e j hArgTrans with
    ⟨A, B, _hATy, _hITy, _hETy, _hJTy, hLhsTy, hRhsTy, _hANonNone,
      hBNonNone, _hATrans, _hITrans, _hETrans, _hJTrans⟩
  rw [prog_arrays_read_over_write_eq a i e j i j]
  rw [requires_and_eq_self_true_body i j body hINotStuck hJNotStuck]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
    (by rw [hLhsTy, hRhsTy])
    (by
      rw [hLhsTy]
      exact hBNonNone)

private theorem facts___eo_prog_arrays_read_over_write_impl
    (M : SmtModel) (hM : model_wf M) (a i e j i2 j2 : Term) :
  RuleProofs.eo_has_smt_translation
    (Term.Apply
      (Term.Apply Term.select
        (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) j) ->
  eo_interprets M
    (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq i2) j2)) true ->
  __eo_typeof
      (__eo_prog_arrays_read_over_write
        (Term.Apply
          (Term.Apply Term.select
            (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) j)
        (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq i2) j2)))) =
    Term.Bool ->
  eo_interprets M
    (__eo_prog_arrays_read_over_write
      (Term.Apply
        (Term.Apply Term.select
          (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) j)
      (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq i2) j2)))) true := by
  intro hArgTrans hPremTrue hResultTy
  let lhs :=
    Term.Apply
      (Term.Apply Term.select
        (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) j
  let rhs := Term.Apply (Term.Apply Term.select a) j
  let body := Term.Apply (Term.Apply Term.eq lhs) rhs
  have hProgBool :
      RuleProofs.eo_has_bool_type
        (__eo_prog_arrays_read_over_write
          (Term.Apply
            (Term.Apply Term.select
              (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) j)
          (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq i2) j2)))) :=
    typed___eo_prog_arrays_read_over_write_impl a i e j i2 j2 hArgTrans hResultTy
  have hProg :
      __eo_prog_arrays_read_over_write
          (Term.Apply
            (Term.Apply Term.select
              (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) j)
          (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq i2) j2))) ≠
        Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type _ hProgBool
  rw [prog_arrays_read_over_write_eq a i e j i2 j2] at hProg
  have hAlign :
      i2 = i ∧ j2 = j :=
    eqs_of_requires_and_eq_true_not_stuck i j i2 j2 body hProg
  have hi2 : i2 = i := hAlign.1
  have hj2 : j2 = j := hAlign.2
  subst i2
  subst j2
  have hINotStuck : i ≠ Term.Stuck := by
    intro hi
    subst i
    simp [__eo_requires, __eo_and, __eo_eq, native_ite,
      native_teq] at hProg
  have hJNotStuck : j ≠ Term.Stuck := by
    intro hj
    subst j
    simp [__eo_requires, __eo_and, __eo_eq, native_ite,
      native_teq] at hProg
  rcases smt_types_of_select_store_arg a i e j hArgTrans with
    ⟨A, B, _hATy, _hITy, _hETy, _hJTy, _hLhsTy, _hRhsTy, _hANonNone,
      _hBNonNone, hATrans, hITrans, hETrans, hJTrans⟩
  have hij :
      native_veq
        (__smtx_model_eval M (__eo_to_smt i))
        (__smtx_model_eval M (__eo_to_smt j)) = false :=
    native_veq_false_of_model_eval_eq_false
      (model_eval_eq_false_of_not_eq_true M i j hPremTrue)
  have hBodyBool : RuleProofs.eo_has_bool_type body := by
    have h := hProgBool
    rw [prog_arrays_read_over_write_eq a i e j i j] at h
    simpa [body, lhs, rhs,
      requires_and_eq_self_true_body i j body hINotStuck hJNotStuck] using h
  rw [prog_arrays_read_over_write_eq a i e j i j]
  rw [requires_and_eq_self_true_body i j body hINotStuck hJNotStuck]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBodyBool <| by
    simpa [lhs, rhs, eo_to_smt_select_eq,
      eo_to_smt_store_eq, __smtx_model_eval] using
      (smt_value_rel_select_store_other_of_native_veq_false
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt i))
        (__smtx_model_eval M (__eo_to_smt j))
        (__smtx_model_eval M (__eo_to_smt e)) hij)

public theorem cmd_step_arrays_read_over_write_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arrays_read_over_write args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arrays_read_over_write args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arrays_read_over_write args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.arrays_read_over_write args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons n1 premises =>
              cases premises with
              | nil =>
                  let P1 := __eo_state_proven_nth s n1
                  have hArgTrans : RuleProofs.eo_has_smt_translation a1 := by
                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                  change __eo_typeof
                      (__eo_prog_arrays_read_over_write a1 (Proof.pf P1)) =
                    Term.Bool at hResultTy
                  have hProgArg :
                      __eo_prog_arrays_read_over_write a1 (Proof.pf P1) ≠
                        Term.Stuck :=
                    term_ne_stuck_of_typeof_bool hResultTy
                  rcases shape_of_prog_arrays_read_over_write_not_stuck
                      a1 P1 hProgArg with
                    ⟨a, i, e, j, i2, j2, hA1, hP1⟩
                  subst a1
                  have hResultTyShape :
                      __eo_typeof
                          (__eo_prog_arrays_read_over_write
                            (Term.Apply
                              (Term.Apply Term.select
                                (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) j)
                            (Proof.pf
                              (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq i2) j2)))) =
                        Term.Bool := by
                    simpa [hP1] using hResultTy
                  refine ⟨?_, ?_⟩
                  · intro hTrue
                    have hPremTrue :
                        eo_interprets M
                          (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq i2) j2))
                          true := by
                      have hStatePremTrue : eo_interprets M P1 true :=
                        hTrue P1 (by simp [P1, premiseTermList])
                      simpa [hP1] using hStatePremTrue
                    change eo_interprets M
                      (__eo_prog_arrays_read_over_write
                        (Term.Apply
                          (Term.Apply Term.select
                            (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) j)
                        (Proof.pf P1)) true
                    simpa [hP1] using
                      facts___eo_prog_arrays_read_over_write_impl M hM
                        a i e j i2 j2 hArgTrans hPremTrue hResultTyShape
                  · change RuleProofs.eo_has_smt_translation
                      (__eo_prog_arrays_read_over_write
                        (Term.Apply
                          (Term.Apply Term.select
                            (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) j)
                        (Proof.pf P1))
                    simpa [hP1] using
                      RuleProofs.eo_has_smt_translation_of_has_bool_type _
                        (typed___eo_prog_arrays_read_over_write_impl
                          a i e j i2 j2 hArgTrans hResultTyShape)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
