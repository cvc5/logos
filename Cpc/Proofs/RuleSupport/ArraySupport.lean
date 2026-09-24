module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.Canonical.Fresh
import all Cpc.Proofs.Canonical.Fresh

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace RuleProofs

theorem eo_to_smt_select_eq (a i : Term) :
    __eo_to_smt (Term.Apply (Term.Apply Term.select a) i) =
      SmtTerm.select (__eo_to_smt a) (__eo_to_smt i) := by
  rfl

theorem eo_to_smt_store_eq (a i e : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e) =
      SmtTerm.store (__eo_to_smt a) (__eo_to_smt i) (__eo_to_smt e) := by
  rfl

theorem eo_to_smt_type_array_of_non_none (A B : Term)
    (h : __eo_to_smt_type (Term.Apply (Term.Apply Term.Array A) B) ≠ SmtType.None) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.Array A) B) =
      SmtType.Map (__eo_to_smt_type A) (__eo_to_smt_type B) := by
  cases hA : __eo_to_smt_type A <;> cases hB : __eo_to_smt_type B <;>
    simp [TranslationProofs.eo_to_smt_type_array, __smtx_typeof_guard,
      native_ite, native_Teq, hA, hB] at h ⊢

theorem eo_typeof_store_not_stuck_implies_array (A I E : Term)
    (h : __eo_typeof_store A I E ≠ Term.Stuck) :
    A = Term.Apply (Term.Apply Term.Array I) E := by
  by_cases hI : I = Term.Stuck
  · subst I
    simp [__eo_typeof_store] at h
  · by_cases hE : E = Term.Stuck
    · subst E
      simp [__eo_typeof_store] at h
    · cases A with
      | Apply f x =>
          cases f with
          | Apply g y =>
              cases g with
              | UOp op =>
                  cases op with
                  | Array =>
                      have hReq :
                          __eo_requires (__eo_and (__eo_eq y I) (__eo_eq x E))
                            (Term.Boolean true) (Term.Apply (Term.Apply Term.Array y) x) ≠
                            Term.Stuck := by
                        simpa [__eo_typeof_store, hI, hE] using h
                      have hEqs :
                          I = y ∧ E = x :=
                        eqs_of_requires_and_eq_true_not_stuck y x I E
                          (Term.Apply (Term.Apply Term.Array y) x) hReq
                      simp [hEqs.1, hEqs.2]
                  | _ =>
                      simp [__eo_typeof_store] at h
              | _ =>
                  simp [__eo_typeof_store] at h
          | _ =>
              simp [__eo_typeof_store] at h
      | _ =>
          simp [__eo_typeof_store] at h

theorem eo_typeof_select_not_stuck_implies_array (A I : Term)
    (h : __eo_typeof_select A I ≠ Term.Stuck) :
    ∃ E : Term, A = Term.Apply (Term.Apply Term.Array I) E := by
  by_cases hI : I = Term.Stuck
  · subst I
    simp [__eo_typeof_select] at h
  · cases A with
    | Apply f x =>
        cases f with
        | Apply g y =>
            cases g with
            | UOp op =>
                cases op with
                | Array =>
                    have hReq :
                        __eo_requires (__eo_eq y I) (Term.Boolean true) x ≠ Term.Stuck := by
                      simpa [__eo_typeof_select, hI] using h
                    have hEq : I = y :=
                      eq_of_requires_eq_true_not_stuck y I x hReq
                    exact ⟨x, by simp [hEq]⟩
                | _ =>
                    simp [__eo_typeof_select] at h
            | _ =>
                simp [__eo_typeof_select] at h
        | _ =>
            simp [__eo_typeof_select] at h
    | _ =>
        simp [__eo_typeof_select] at h

theorem smt_value_rel_map_of_lookup_eq
    (m1 m2 : SmtMap)
    (hm1 : __smtx_map_canonical m1 = true)
    (hm2 : __smtx_map_canonical m2 = true)
    (hDef : Smtm.smt_map_default_leaf m1 = Smtm.smt_map_default_leaf m2)
    (h : ∀ v : SmtValue, __smtx_map_lookup m1 v = __smtx_map_lookup m2 v) :
    smt_value_rel (SmtValue.Map m1) (SmtValue.Map m2) := by
  have hEq : m1 = m2 := Smtm.map_ext_of_lookup_eq hm1 hm2 hDef h
  subst m2
  exact smt_value_rel_refl (SmtValue.Map m1)

theorem smt_value_rel_set_of_lookup_eq
    (m1 m2 : SmtMap)
    (hm1 : __smtx_map_canonical m1 = true)
    (hm2 : __smtx_map_canonical m2 = true)
    (hDef : Smtm.smt_map_default_leaf m1 = Smtm.smt_map_default_leaf m2)
    (h : ∀ v : SmtValue, __smtx_map_lookup m1 v = __smtx_map_lookup m2 v) :
    smt_value_rel (SmtValue.Set m1) (SmtValue.Set m2) := by
  have hEq : m1 = m2 := Smtm.map_ext_of_lookup_eq hm1 hm2 hDef h
  subst m2
  exact smt_value_rel_refl (SmtValue.Set m1)

theorem smt_value_rel_select_store_same_of_map
    (m : SmtMap) (i e : SmtValue)
    (hm : __smtx_map_canonical m = true)
    (hi : value_canonical i)
    (he : value_canonical e) :
    smt_value_rel
      (__smtx_model_eval_select (__smtx_model_eval_store (SmtValue.Map m) i e) i)
      e := by
  have hLookup :
      __smtx_model_eval_select
          (__smtx_model_eval_store (SmtValue.Map m) i e) i = e := by
    simpa [__smtx_model_eval_select, __smtx_model_eval_store,
      __smtx_map_select, __smtx_map_store] using
      Smtm.map_lookup_update_aux_same (m := m) (i := i) (e := e) hm
  rw [hLookup]
  exact smt_value_rel_refl e

private theorem eq_of_native_veq_true {v1 v2 : SmtValue}
    (h : native_veq v1 v2 = true) :
    v1 = v2 := by
  simpa [native_veq] using h

theorem smt_value_rel_store_overwrite
    (v i e f : SmtValue)
    (hv : value_canonical v)
    (hi : value_canonical i)
    (he : value_canonical e)
    (hf : value_canonical f) :
    smt_value_rel
      (__smtx_model_eval_store (__smtx_model_eval_store v i e) i f)
      (__smtx_model_eval_store v i f) := by
  cases v <;>
    try
      simpa [__smtx_model_eval_store, __smtx_map_store] using
        smt_value_rel_refl SmtValue.NotValue
  · have hm : __smtx_map_canonical ‹SmtMap› = true := by
      first
      | simpa [value_canonical, __smtx_value_canonical] using hv
      | have hParts := hv
        simp [value_canonical, __smtx_value_canonical,
          SmtEval.native_and] at hParts
        exact hParts.1
    have hmInner :
        __smtx_map_canonical
          (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› i e) = true :=
      Smtm.map_update_aux_canonical (m := ‹SmtMap›) (i := i) (e := e) hm hi he
    have hmLeft :
        __smtx_map_canonical
          (__smtx_map_update_aux
            (__smtx_map_get_default
              (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› i e))
            (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› i e)
            i f) = true :=
      Smtm.map_update_aux_canonical
        (m := __smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› i e)
        (i := i) (e := f) hmInner hi hf
    have hmRight :
        __smtx_map_canonical
          (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› i f) = true :=
      Smtm.map_update_aux_canonical (m := ‹SmtMap›) (i := i) (e := f) hm hi hf
    simpa [__smtx_model_eval_store, __smtx_map_store] using
      smt_value_rel_map_of_lookup_eq
        (__smtx_map_update_aux
          (__smtx_map_get_default
            (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› i e))
          (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› i e)
          i f)
        (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› i f)
        hmLeft hmRight
        (by simp [Smtm.map_update_aux_default_leaf])
        (by
          intro x
          exact Smtm.map_lookup_update_aux_overwrite
            (m := ‹SmtMap›) (i := i) (e := e) (f := f) (x := x) hm hi he)
  · have hm : __smtx_map_canonical ‹SmtMap› = true := by
      first
      | simpa [value_canonical, __smtx_value_canonical] using hv
      | have hParts := hv
        simp [value_canonical, __smtx_value_canonical,
          SmtEval.native_and] at hParts
        exact hParts.1
    have hmInner :
        __smtx_map_canonical
          (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› i e) = true :=
      Smtm.map_update_aux_canonical (m := ‹SmtMap›) (i := i) (e := e) hm hi he
    have hmLeft :
        __smtx_map_canonical
          (__smtx_map_update_aux
            (__smtx_map_get_default
              (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› i e))
            (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› i e)
            i f) = true :=
      Smtm.map_update_aux_canonical
        (m := __smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› i e)
        (i := i) (e := f) hmInner hi hf
    have hmRight :
        __smtx_map_canonical
          (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› i f) = true :=
      Smtm.map_update_aux_canonical (m := ‹SmtMap›) (i := i) (e := f) hm hi hf
    simpa [__smtx_model_eval_store, __smtx_map_store] using
      smt_value_rel_set_of_lookup_eq
        (__smtx_map_update_aux
          (__smtx_map_get_default
            (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› i e))
          (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› i e)
          i f)
        (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› i f)
        hmLeft hmRight
        (by simp [Smtm.map_update_aux_default_leaf])
        (by
          intro x
          exact Smtm.map_lookup_update_aux_overwrite
            (m := ‹SmtMap›) (i := i) (e := e) (f := f) (x := x) hm hi he)

theorem smt_value_rel_store_swap_of_native_veq_false
    (v i j e f : SmtValue)
    (hv : value_canonical v)
    (hi : value_canonical i)
    (hj : value_canonical j)
    (he : value_canonical e)
    (hf : value_canonical f)
    (hij : native_veq i j = false) :
    smt_value_rel
      (__smtx_model_eval_store (__smtx_model_eval_store v i e) j f)
      (__smtx_model_eval_store (__smtx_model_eval_store v j f) i e) := by
  cases v <;>
    try
      simpa [__smtx_model_eval_store, __smtx_map_store] using
        smt_value_rel_refl SmtValue.NotValue
  · have hm : __smtx_map_canonical ‹SmtMap› = true := by
      first
      | simpa [value_canonical, __smtx_value_canonical] using hv
      | have hParts := hv
        simp [value_canonical, __smtx_value_canonical,
          SmtEval.native_and] at hParts
        exact hParts.1
    have hmi :
        __smtx_map_canonical
          (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› i e) = true :=
      Smtm.map_update_aux_canonical (m := ‹SmtMap›) (i := i) (e := e) hm hi he
    have hmj :
        __smtx_map_canonical
          (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› j f) = true :=
      Smtm.map_update_aux_canonical (m := ‹SmtMap›) (i := j) (e := f) hm hj hf
    have hmLeft :
        __smtx_map_canonical
          (__smtx_map_update_aux
            (__smtx_map_get_default
              (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› i e))
            (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› i e)
            j f) = true :=
      Smtm.map_update_aux_canonical
        (m := __smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› i e)
        (i := j) (e := f) hmi hj hf
    have hmRight :
        __smtx_map_canonical
          (__smtx_map_update_aux
            (__smtx_map_get_default
              (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› j f))
            (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› j f)
            i e) = true :=
      Smtm.map_update_aux_canonical
        (m := __smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› j f)
        (i := i) (e := e) hmj hi he
    simpa [__smtx_model_eval_store, __smtx_map_store] using
      smt_value_rel_map_of_lookup_eq
        (__smtx_map_update_aux
          (__smtx_map_get_default
            (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› i e))
          (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› i e)
          j f)
        (__smtx_map_update_aux
          (__smtx_map_get_default
            (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› j f))
          (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› j f)
          i e)
        hmLeft hmRight
        (by simp [Smtm.map_update_aux_default_leaf])
        (by
          intro x
          exact Smtm.map_lookup_update_aux_swap
            (m := ‹SmtMap›) (i := i) (j := j) (e := e) (f := f) (x := x)
            hm hi hj he hf hij)
  · have hm : __smtx_map_canonical ‹SmtMap› = true := by
      first
      | simpa [value_canonical, __smtx_value_canonical] using hv
      | have hParts := hv
        simp [value_canonical, __smtx_value_canonical,
          SmtEval.native_and] at hParts
        exact hParts.1
    have hmi :
        __smtx_map_canonical
          (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› i e) = true :=
      Smtm.map_update_aux_canonical (m := ‹SmtMap›) (i := i) (e := e) hm hi he
    have hmj :
        __smtx_map_canonical
          (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› j f) = true :=
      Smtm.map_update_aux_canonical (m := ‹SmtMap›) (i := j) (e := f) hm hj hf
    have hmLeft :
        __smtx_map_canonical
          (__smtx_map_update_aux
            (__smtx_map_get_default
              (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› i e))
            (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› i e)
            j f) = true :=
      Smtm.map_update_aux_canonical
        (m := __smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› i e)
        (i := j) (e := f) hmi hj hf
    have hmRight :
        __smtx_map_canonical
          (__smtx_map_update_aux
            (__smtx_map_get_default
              (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› j f))
            (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› j f)
            i e) = true :=
      Smtm.map_update_aux_canonical
        (m := __smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› j f)
        (i := i) (e := e) hmj hi he
    simpa [__smtx_model_eval_store, __smtx_map_store] using
      smt_value_rel_set_of_lookup_eq
        (__smtx_map_update_aux
          (__smtx_map_get_default
            (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› i e))
          (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› i e)
          j f)
        (__smtx_map_update_aux
          (__smtx_map_get_default
            (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› j f))
          (__smtx_map_update_aux (__smtx_map_get_default ‹SmtMap›) ‹SmtMap› j f)
          i e)
        hmLeft hmRight
        (by simp [Smtm.map_update_aux_default_leaf])
        (by
          intro x
          exact Smtm.map_lookup_update_aux_swap
            (m := ‹SmtMap›) (i := i) (j := j) (e := e) (f := f) (x := x)
            hm hi hj he hf hij)

theorem smt_value_rel_select_store_other_of_native_veq_false
    (v i j e : SmtValue)
    (hv : value_canonical v)
    (hi : value_canonical i)
    (hj : value_canonical j)
    (he : value_canonical e)
    (hij : native_veq i j = false) :
    smt_value_rel
      (__smtx_model_eval_select (__smtx_model_eval_store v i e) j)
      (__smtx_model_eval_select v j) := by
  cases v <;>
    try
      simpa [__smtx_model_eval_select, __smtx_model_eval_store,
        __smtx_map_select, __smtx_map_store] using
        smt_value_rel_refl SmtValue.NotValue
  · have hm : __smtx_map_canonical ‹SmtMap› = true := by
      first
      | simpa [value_canonical, __smtx_value_canonical] using hv
      | have hParts := hv
        simp [value_canonical, __smtx_value_canonical,
          SmtEval.native_and] at hParts
        exact hParts.1
    have hLookup :
        __smtx_model_eval_select
            (__smtx_model_eval_store (SmtValue.Map ‹SmtMap›) i e) j =
          __smtx_model_eval_select (SmtValue.Map ‹SmtMap›) j := by
      simpa [__smtx_model_eval_select, __smtx_model_eval_store,
        __smtx_map_select, __smtx_map_store] using
        Smtm.map_lookup_update_aux_other (m := ‹SmtMap›)
          (i := i) (j := j) (e := e) hm hij
    rw [hLookup]
    exact smt_value_rel_refl (__smtx_model_eval_select (SmtValue.Map ‹SmtMap›) j)
  · have hm : __smtx_map_canonical ‹SmtMap› = true := by
      first
      | simpa [value_canonical, __smtx_value_canonical] using hv
      | have hParts := hv
        simp [value_canonical, __smtx_value_canonical,
          SmtEval.native_and] at hParts
        exact hParts.1
    have hLookup :
        __smtx_model_eval_select
            (__smtx_model_eval_store (SmtValue.Set ‹SmtMap›) i e) j =
          __smtx_model_eval_select (SmtValue.Set ‹SmtMap›) j := by
      simpa [__smtx_model_eval_select, __smtx_model_eval_store,
        __smtx_map_select, __smtx_map_store] using
        Smtm.map_lookup_update_aux_other (m := ‹SmtMap›)
          (i := i) (j := j) (e := e) hm hij
    rw [hLookup]
    exact smt_value_rel_refl (__smtx_model_eval_select (SmtValue.Set ‹SmtMap›) j)

theorem smt_value_rel_store_self_of_map
    (m : SmtMap) (i : SmtValue)
    (hm : __smtx_map_canonical m = true)
    (hi : value_canonical i) :
    smt_value_rel
      (__smtx_model_eval_store
        (SmtValue.Map m) i
        (__smtx_model_eval_select (SmtValue.Map m) i))
      (SmtValue.Map m) := by
  have hLookupCanonical : value_canonical (__smtx_map_lookup m i) :=
    Smtm.map_lookup_value_canonical (m := m) (i := i) hm
  have hmLeft :
      __smtx_map_canonical
        (__smtx_map_update_aux (__smtx_map_get_default m) m i
          (__smtx_map_lookup m i)) = true :=
    Smtm.map_update_aux_canonical
      (m := m) (i := i) (e := __smtx_map_lookup m i) hm hi hLookupCanonical
  simpa [__smtx_model_eval_store, __smtx_model_eval_select,
    __smtx_map_store, __smtx_map_select] using
    smt_value_rel_map_of_lookup_eq
      (__smtx_map_update_aux (__smtx_map_get_default m) m i
        (__smtx_map_lookup m i))
      m
      hmLeft hm
      (by simp [Smtm.map_update_aux_default_leaf])
      (by
        intro x
        exact Smtm.map_lookup_update_aux_self (m := m) (i := i) (x := x) hm)

private theorem model_eval_eq_false_of_native_veq_false_non_reglan
    {v1 v2 : SmtValue} {B : SmtType}
    (hTy1 : __smtx_typeof_value v1 = B)
    (hTy2 : __smtx_typeof_value v2 = B)
    (hB : B ≠ SmtType.RegLan)
    (hNe : native_veq v1 v2 = false) :
    __smtx_model_eval_eq v1 v2 = SmtValue.Boolean false := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_eq, native_veq, __smtx_typeof_value] at hTy1 hTy2 hB hNe ⊢
  all_goals try assumption
  exact False.elim (hB hTy1.symm)

private theorem map_default_eq_type_default_of_finite_domain :
    ∀ {m : SmtMap} {A B : SmtType},
      __smtx_typeof_map_value m = SmtType.Map A B ->
        __smtx_map_canonical m = true ->
          __smtx_is_finite_type A = true ->
            __smtx_map_get_default m = __smtx_type_default B
  | SmtMap.default T e, A, B, hTy, hCan, hFin => by
      cases hTy
      have hParts := hCan
      simp [__smtx_map_canonical, __smtx_map_default_canonical, hFin,
        native_ite, SmtEval.native_and] at hParts
      exact Smtm.eq_of_native_veq_true hParts.1
  | SmtMap.cons i e m, A, B, hTy, hCan, hFin => by
      have hmTy : __smtx_typeof_map_value m = SmtType.Map A B := by
        by_cases hEq :
            native_Teq
              (SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e))
              (__smtx_typeof_map_value m)
        · simpa [__smtx_typeof_map_value, native_ite, hEq] using hTy
        · simp [__smtx_typeof_map_value, native_ite, hEq] at hTy
      have hmCan : __smtx_map_canonical m = true := by
        have hParts := hCan
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        exact hParts.1.1.2
      simpa [__smtx_map_get_default] using
        map_default_eq_type_default_of_finite_domain hmTy hmCan hFin

private theorem map_default_leaf_eq_default_of_type :
    ∀ {m : SmtMap} {A B : SmtType},
      __smtx_typeof_map_value m = SmtType.Map A B ->
        Smtm.smt_map_default_leaf m =
          SmtMap.default A (__smtx_map_get_default m)
  | SmtMap.default T e, A, B, hTy => by
      cases hTy
      rfl
  | SmtMap.cons i e m, A, B, hTy => by
      have hmTy : __smtx_typeof_map_value m = SmtType.Map A B := by
        by_cases hEq :
            native_Teq
              (SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e))
              (__smtx_typeof_map_value m)
        · simpa [__smtx_typeof_map_value, native_ite, hEq] using hTy
        · simp [__smtx_typeof_map_value, native_ite, hEq] at hTy
      simpa [Smtm.smt_map_default_leaf, __smtx_map_get_default] using
        map_default_leaf_eq_default_of_type hmTy

private theorem map_default_leaf_eq_of_get_default_eq
    {m1 m2 : SmtMap} {A B : SmtType}
    (h1 : __smtx_typeof_map_value m1 = SmtType.Map A B)
    (h2 : __smtx_typeof_map_value m2 = SmtType.Map A B)
    (hDef : __smtx_map_get_default m1 = __smtx_map_get_default m2) :
    Smtm.smt_map_default_leaf m1 = Smtm.smt_map_default_leaf m2 := by
  rw [map_default_leaf_eq_default_of_type h1,
    map_default_leaf_eq_default_of_type h2, hDef]

private theorem map_lookup_eq_default_of_not_typed_canonical :
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
          map_lookup_eq_default_of_not_typed_canonical hmTy hmCan hNot
        simpa [__smtx_map_lookup, __smtx_map_get_default, native_ite,
          hivFalse] using hRec

/--
Fresh-index witness needed only for the infinite-domain branch of array
extensionality.  Discharged by the `Canonical.Fresh` freshness stack; the
residual datatype obligations live behind
`Smtm.infinite_datatype_large_witness` /
`Smtm.finite_nonunit_datatype_nondefault_value`.
-/
private theorem fresh_default_lookup_for_infinite_map_domain
    (m1 m2 : SmtMap)
    (A B : SmtType)
    (_hm1Ty : __smtx_typeof_map_value m1 = SmtType.Map A B)
    (_hm2Ty : __smtx_typeof_map_value m2 = SmtType.Map A B)
    (_hm1Can : __smtx_map_canonical m1 = true)
    (_hm2Can : __smtx_map_canonical m2 = true)
    (_hAInh : native_inhabited_type A = true)
    (_hARec : __smtx_type_wf_rec A = true)
    (_hInfinite : __smtx_is_finite_type A = false) :
    ∃ i : SmtValue,
      __smtx_typeof_value i = A ∧
        __smtx_value_canonical i = true ∧
          __smtx_map_lookup m1 i = __smtx_map_get_default m1 ∧
            __smtx_map_lookup m2 i = __smtx_map_get_default m2 :=
  Smtm.fresh_default_lookup_for_infinite_map_domain m1 m2 A B
    _hm1Ty _hm2Ty _hm1Can _hm2Can _hAInh _hARec _hInfinite

private theorem map_defaults_eq_of_no_typed_canonical_lookup_diff
    {m1 m2 : SmtMap} {A B : SmtType}
    (hm1Ty : __smtx_typeof_map_value m1 = SmtType.Map A B)
    (hm2Ty : __smtx_typeof_map_value m2 = SmtType.Map A B)
    (hm1Can : __smtx_map_canonical m1 = true)
    (hm2Can : __smtx_map_canonical m2 = true)
    (hAInh : native_inhabited_type A = true)
    (hARec : __smtx_type_wf_rec A = true)
    (hNoDiff :
      ¬ ∃ i : SmtValue,
        __smtx_typeof_value i = A ∧
          __smtx_value_canonical i = true ∧
            native_veq (__smtx_map_lookup m1 i)
              (__smtx_map_lookup m2 i) = false) :
    __smtx_map_get_default m1 = __smtx_map_get_default m2 := by
  cases hFin : __smtx_is_finite_type A
  · rcases fresh_default_lookup_for_infinite_map_domain
        m1 m2 A B hm1Ty hm2Ty hm1Can hm2Can hAInh hARec hFin with
      ⟨i, hiTy, hiCan, hiLookup1, hiLookup2⟩
    cases hVeq :
        native_veq (__smtx_map_get_default m1)
          (__smtx_map_get_default m2)
    · exact False.elim
        (hNoDiff ⟨i, hiTy, hiCan, by
          simpa [hiLookup1, hiLookup2] using hVeq⟩)
    · exact Smtm.eq_of_native_veq_true hVeq
  · calc
      __smtx_map_get_default m1 = __smtx_type_default B :=
        map_default_eq_type_default_of_finite_domain hm1Ty hm1Can hFin
      _ = __smtx_map_get_default m2 :=
        (map_default_eq_type_default_of_finite_domain hm2Ty hm2Can hFin).symm

private theorem map_diff_typed_canonical_lookup_witness
    (m1 m2 : SmtMap)
    (A B : SmtType)
    (hm1Ty : __smtx_typeof_map_value m1 = SmtType.Map A B)
    (hm2Ty : __smtx_typeof_map_value m2 = SmtType.Map A B)
    (hm1Can : __smtx_map_canonical m1 = true)
    (hm2Can : __smtx_map_canonical m2 = true)
    (hAInh : native_inhabited_type A = true)
    (hARec : __smtx_type_wf_rec A = true)
    (hNe : __smtx_model_eval_eq (SmtValue.Map m1) (SmtValue.Map m2) =
      SmtValue.Boolean false) :
    ∃ i : SmtValue,
      __smtx_typeof_value i = A ∧
        __smtx_value_canonical i = true ∧
          native_veq (__smtx_map_lookup m1 i)
            (__smtx_map_lookup m2 i) = false := by
  by_cases hDiff :
      ∃ i : SmtValue,
        __smtx_typeof_value i = A ∧
          __smtx_value_canonical i = true ∧
            native_veq (__smtx_map_lookup m1 i)
              (__smtx_map_lookup m2 i) = false
  · exact hDiff
  · exfalso
    have hDefaultEq :
        __smtx_map_get_default m1 = __smtx_map_get_default m2 :=
      map_defaults_eq_of_no_typed_canonical_lookup_diff
        hm1Ty hm2Ty hm1Can hm2Can hAInh hARec hDiff
    have hLeafEq :
        Smtm.smt_map_default_leaf m1 = Smtm.smt_map_default_leaf m2 :=
      map_default_leaf_eq_of_get_default_eq hm1Ty hm2Ty hDefaultEq
    have hLookupEq :
        ∀ v : SmtValue, __smtx_map_lookup m1 v = __smtx_map_lookup m2 v := by
      intro v
      by_cases hv :
          __smtx_typeof_value v = A ∧ __smtx_value_canonical v = true
      · have hNotFalse :
            native_veq (__smtx_map_lookup m1 v)
              (__smtx_map_lookup m2 v) ≠ false := by
          intro hFalse
          exact hDiff ⟨v, hv.1, hv.2, hFalse⟩
        cases hVeq :
            native_veq (__smtx_map_lookup m1 v) (__smtx_map_lookup m2 v)
        · exact False.elim (hNotFalse hVeq)
        · exact Smtm.eq_of_native_veq_true hVeq
      · calc
          __smtx_map_lookup m1 v = __smtx_map_get_default m1 :=
            map_lookup_eq_default_of_not_typed_canonical hm1Ty hm1Can hv
          _ = __smtx_map_get_default m2 := hDefaultEq
          _ = __smtx_map_lookup m2 v :=
            (map_lookup_eq_default_of_not_typed_canonical hm2Ty hm2Can hv).symm
    have hEq : m1 = m2 :=
      Smtm.map_ext_of_lookup_eq hm1Can hm2Can hLeafEq hLookupEq
    subst m2
    simp [__smtx_model_eval_eq, native_veq] at hNe

theorem map_diff_selects_model_eval_eq_false_of_default_eq
    (m1 m2 : SmtMap)
    (A B : SmtType)
    (hm1Ty : __smtx_typeof_map_value m1 = SmtType.Map A B)
    (hm2Ty : __smtx_typeof_map_value m2 = SmtType.Map A B)
    (hm1Can : __smtx_map_canonical m1 = true)
    (hm2Can : __smtx_map_canonical m2 = true)
    (hDefaultEq : __smtx_map_get_default m1 = __smtx_map_get_default m2)
    (hBNeRegLan : B ≠ SmtType.RegLan)
    (hNe : __smtx_model_eval_eq (SmtValue.Map m1) (SmtValue.Map m2) =
      SmtValue.Boolean false) :
    __smtx_model_eval_eq
        (__smtx_map_lookup m1 (native_eval_map_diff m1 m2))
        (__smtx_map_lookup m2 (native_eval_map_diff m1 m2)) =
      SmtValue.Boolean false := by
  classical
  change
    __smtx_model_eval_eq
        (__smtx_map_lookup m1 (native_eval_map_diff m1 m2))
        (__smtx_map_lookup m2 (native_eval_map_diff m1 m2)) =
      SmtValue.Boolean false
  rw [hm1Ty, hm2Ty]
  simp [native_ite, native_Teq, SmtEval.native_and]
  by_cases hDiff :
      ∃ i : SmtValue,
        __smtx_typeof_value i = A ∧
          __smtx_value_canonical i = true ∧
            native_veq (__smtx_map_lookup m1 i)
              (__smtx_map_lookup m2 i) = false
  · have hSpec := Classical.choose_spec hDiff
    have hLookup1Ty :
        __smtx_typeof_value
            (__smtx_map_lookup m1 (Classical.choose hDiff)) = B :=
      Smtm.map_lookup_typed hm1Ty hSpec.1
    have hLookup2Ty :
        __smtx_typeof_value
            (__smtx_map_lookup m2 (Classical.choose hDiff)) = B :=
      Smtm.map_lookup_typed hm2Ty hSpec.1
    have hFalse :
        __smtx_model_eval_eq
            (__smtx_map_lookup m1 (Classical.choose hDiff))
            (__smtx_map_lookup m2 (Classical.choose hDiff)) =
          SmtValue.Boolean false :=
      model_eval_eq_false_of_native_veq_false_non_reglan
        hLookup1Ty hLookup2Ty hBNeRegLan hSpec.2.2
    simpa [hDiff] using hFalse
  · exfalso
    have hLeafEq :
        Smtm.smt_map_default_leaf m1 = Smtm.smt_map_default_leaf m2 :=
      map_default_leaf_eq_of_get_default_eq hm1Ty hm2Ty hDefaultEq
    have hLookupEq :
        ∀ v : SmtValue, __smtx_map_lookup m1 v = __smtx_map_lookup m2 v := by
      intro v
      by_cases hv :
          __smtx_typeof_value v = A ∧ __smtx_value_canonical v = true
      · have hNotFalse :
            native_veq (__smtx_map_lookup m1 v)
              (__smtx_map_lookup m2 v) ≠ false := by
          intro hFalse
          exact hDiff ⟨v, hv.1, hv.2, hFalse⟩
        cases hVeq :
            native_veq (__smtx_map_lookup m1 v) (__smtx_map_lookup m2 v)
        · exact False.elim (hNotFalse hVeq)
        · exact Smtm.eq_of_native_veq_true hVeq
      · calc
          __smtx_map_lookup m1 v = __smtx_map_get_default m1 :=
            map_lookup_eq_default_of_not_typed_canonical hm1Ty hm1Can hv
          _ = __smtx_map_get_default m2 := hDefaultEq
          _ = __smtx_map_lookup m2 v :=
            (map_lookup_eq_default_of_not_typed_canonical hm2Ty hm2Can hv).symm
    have hEq : m1 = m2 :=
      Smtm.map_ext_of_lookup_eq hm1Can hm2Can hLeafEq hLookupEq
    subst m2
    simp [__smtx_model_eval_eq, native_veq] at hNe

theorem map_diff_selects_model_eval_eq_false
    (m1 m2 : SmtMap)
    (A B : SmtType)
    (hm1Ty : __smtx_typeof_map_value m1 = SmtType.Map A B)
    (hm2Ty : __smtx_typeof_map_value m2 = SmtType.Map A B)
    (hm1Can : __smtx_map_canonical m1 = true)
    (hm2Can : __smtx_map_canonical m2 = true)
    (hAInh : native_inhabited_type A = true)
    (hARec : __smtx_type_wf_rec A = true)
    (hBNeRegLan : B ≠ SmtType.RegLan)
    (hNe : __smtx_model_eval_eq (SmtValue.Map m1) (SmtValue.Map m2) =
      SmtValue.Boolean false) :
    __smtx_model_eval_eq
        (__smtx_map_lookup m1 (native_eval_map_diff m1 m2))
        (__smtx_map_lookup m2 (native_eval_map_diff m1 m2)) =
      SmtValue.Boolean false := by
  classical
  change
    __smtx_model_eval_eq
        (__smtx_map_lookup m1 (native_eval_map_diff m1 m2))
        (__smtx_map_lookup m2 (native_eval_map_diff m1 m2)) =
      SmtValue.Boolean false
  rw [hm1Ty, hm2Ty]
  simp [native_ite, native_Teq, SmtEval.native_and]
  by_cases hDiff :
      ∃ i : SmtValue,
        __smtx_typeof_value i = A ∧
          __smtx_value_canonical i = true ∧
            native_veq (__smtx_map_lookup m1 i)
              (__smtx_map_lookup m2 i) = false
  · have hSpec := Classical.choose_spec hDiff
    have hLookup1Ty :
        __smtx_typeof_value
            (__smtx_map_lookup m1 (Classical.choose hDiff)) = B :=
      Smtm.map_lookup_typed hm1Ty hSpec.1
    have hLookup2Ty :
        __smtx_typeof_value
            (__smtx_map_lookup m2 (Classical.choose hDiff)) = B :=
      Smtm.map_lookup_typed hm2Ty hSpec.1
    have hFalse :
        __smtx_model_eval_eq
            (__smtx_map_lookup m1 (Classical.choose hDiff))
            (__smtx_map_lookup m2 (Classical.choose hDiff)) =
          SmtValue.Boolean false :=
      model_eval_eq_false_of_native_veq_false_non_reglan
        hLookup1Ty hLookup2Ty hBNeRegLan hSpec.2.2
    simpa [hDiff] using hFalse
  · exact False.elim (hDiff
      (map_diff_typed_canonical_lookup_witness
        m1 m2 A B hm1Ty hm2Ty hm1Can hm2Can hAInh hARec hNe))

end RuleProofs
