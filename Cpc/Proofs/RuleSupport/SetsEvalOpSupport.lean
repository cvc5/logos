module

public import Cpc.Proofs.RuleSupport.SetsMemberSupport
import all Cpc.Proofs.RuleSupport.SetsMemberSupport
public import Cpc.Proofs.RuleSupport.ArraySupport
import all Cpc.Proofs.RuleSupport.ArraySupport
public import Cpc.Proofs.RuleSupport.DistinctTermsSupport
import all Cpc.Proofs.RuleSupport.DistinctTermsSupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace SetsEvalOpSupport

open SetsMemberSupport

/--
`listLookup M L v` is the membership characteristic value of `v` in the model
interpretation of a cons-shaped element list `L` (a `@@TypedList` produced by
`__set_union_to_list` / `__eval_sets_op`, or a raw `__eo_List` produced by
`__eo_get_elements_rec`). It returns `Boolean true` iff the model value `v` equals
the model evaluation of some element term of `L`, mirroring the SMT model lookups
of a union-of-singletons set value.
-/
noncomputable def listLookup (M : SmtModel) : Term -> SmtValue -> SmtValue
  | Term.Apply (Term.Apply _ x) y, v =>
      native_ite (native_veq (__smtx_model_eval M (__eo_to_smt x)) v)
        (SmtValue.Boolean true) (listLookup M y v)
  | _, v => SmtValue.Boolean false

theorem listLookup_cons (M : SmtModel) (f x y : Term) (v : SmtValue) :
    listLookup M (Term.Apply (Term.Apply f x) y) v =
      native_ite (native_veq (__smtx_model_eval M (__eo_to_smt x)) v)
        (SmtValue.Boolean true) (listLookup M y v) := by
  rfl

/-! ### Foundational set-value lemmas -/

/-- The default leaf of a canonical, Bool-valued, default-false set map is
`SmtMap.default A (Boolean false)`. -/
theorem set_default_leaf :
    ∀ {m : SmtMap} {A : SmtType},
      __smtx_map_canonical m = true ->
      __smtx_typeof_map_value m = SmtType.Map A SmtType.Bool ->
      __smtx_map_get_default m = SmtValue.Boolean false ->
      smt_map_default_leaf m = SmtMap.default A (SmtValue.Boolean false)
  | SmtMap.default T e, A, _hCan, hTy, hDef => by
      have hT : T = A := by
        have := hTy
        simp [__smtx_typeof_map_value] at this
        exact this.1
      have he : e = SmtValue.Boolean false := by
        simpa [__smtx_map_get_default] using hDef
      subst hT; subst he
      rfl
  | SmtMap.cons k v m, A, hCan, hTy, hDef => by
      have hTailTy : __smtx_typeof_map_value m = SmtType.Map A SmtType.Bool :=
        map_cons_tail_type hTy
      have hTailCan : __smtx_map_canonical m = true :=
        map_cons_tail_canonical hCan
      have hTailDef : __smtx_map_get_default m = SmtValue.Boolean false := by
        simpa [__smtx_map_get_default] using hDef
      have hRec := set_default_leaf hTailCan hTailTy hTailDef
      simpa [smt_map_default_leaf] using hRec

/-- Lookup of a union of two canonical, Bool-valued, default-false set maps. -/
theorem set_union_lookup
    (m1 m2 : SmtMap) (A : SmtType) (v : SmtValue)
    (h1Ty : __smtx_typeof_map_value m1 = SmtType.Map A SmtType.Bool)
    (h2Ty : __smtx_typeof_map_value m2 = SmtType.Map A SmtType.Bool)
    (h1Can : __smtx_map_canonical m1 = true)
    (h2Can : __smtx_map_canonical m2 = true)
    (h1Def : __smtx_map_get_default m1 = SmtValue.Boolean false) :
    __smtx_map_lookup
        (__smtx_set_op_rec false m1
          (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m1))
            (SmtValue.Boolean false)) m2) v =
      native_ite
        (native_veq (__smtx_map_lookup m1 v) (SmtValue.Boolean true))
        (SmtValue.Boolean true)
        (__smtx_map_lookup m2 v) := by
  have hEmptyTy :
      __smtx_typeof_map_value
          (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m1))
            (SmtValue.Boolean false)) = SmtType.Map A SmtType.Bool := by
    rw [h1Ty]
    simp [__smtx_index_typeof_map, __smtx_typeof_map_value, __smtx_typeof_value]
  have hRec :=
    mss_op_lookup_acc false (m1 := m1)
      (m2 := SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m1))
        (SmtValue.Boolean false))
      (acc := m2) (A := A) (i := v) h1Ty hEmptyTy h2Ty h1Can h2Can h1Def
  rw [hRec]
  simp [__smtx_map_lookup, native_veq, native_iff, SmtEval.native_and, native_ite]

/-- The model value of a set-typed translated term is a canonical, Bool-valued,
default-false set map. -/
theorem set_value_facts
    (M : SmtModel) (hM : model_wf M) (t : Term) (A : SmtType)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    (hTyA : __smtx_typeof (__eo_to_smt t) = SmtType.Set A) :
    ∃ m : SmtMap,
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.Set m ∧
        __smtx_map_canonical m = true ∧
          __smtx_typeof_map_value m = SmtType.Map A SmtType.Bool ∧
            __smtx_map_get_default m = SmtValue.Boolean false := by
  have hCanEval : value_canonical (__smtx_model_eval M (__eo_to_smt t)) :=
    RuleProofs.model_eval_eo_to_smt_canonical M hM t hTrans
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) = SmtType.Set A := by
    simpa [hTyA] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
        (by
          simpa [term_has_non_none_type, RuleProofs.eo_has_smt_translation]
            using hTrans)
  rcases set_value_canonical hEvalTy with ⟨m, hm⟩
  have hCanSet : value_canonical (SmtValue.Set m) := by
    simpa [hm] using hCanEval
  have hmCan : __smtx_map_canonical m = true := by
    have hParts := hCanSet
    simp [value_canonical, __smtx_value_canonical, SmtEval.native_and]
      at hParts
    exact hParts.1
  have hmDef : __smtx_map_get_default m = SmtValue.Boolean false := by
    have hParts := hCanSet
    simp [value_canonical, __smtx_value_canonical, SmtEval.native_and]
      at hParts
    exact eq_of_native_veq_true hParts.2
  have hmTy : __smtx_typeof_map_value m = SmtType.Map A SmtType.Bool :=
    set_map_value_typed (by simpa [hm] using hEvalTy)
  exact ⟨m, hm, hmCan, hmTy, hmDef⟩

/-! ### Element-list predicate and list-level lemmas -/

/-- A cons-shaped element list: a chain of `Apply (Apply _ _)` cells terminating in
a non-`Stuck`, non-cons terminator (e.g. a `@@TypedList_nil`/`__eo_List_nil`). -/
def IsElemList : Term -> Prop
  | Term.Apply (Term.Apply f x) y => f ≠ Term.Stuck ∧ x ≠ Term.Stuck ∧ IsElemList y
  | Term.Stuck => False
  | _ => True

theorem isElemList_ne_stuck {L : Term} (h : IsElemList L) : L ≠ Term.Stuck := by
  intro hStuck; rw [hStuck] at h; exact h

theorem mk_apply_of_ne_stuck {a w : Term} (ha : a ≠ Term.Stuck) (hw : w ≠ Term.Stuck) :
    __eo_mk_apply a w = Term.Apply a w := by
  cases a <;> cases w <;> simp_all [__eo_mk_apply]

/-- Reduction of `__eo_list_concat_rec` on a cons cell with non-`Stuck` second list. -/
theorem concat_rec_cons (f x y z : Term) (hz : z ≠ Term.Stuck) :
    __eo_list_concat_rec (Term.Apply (Term.Apply f x) y) z =
      __eo_mk_apply (Term.Apply f x) (__eo_list_concat_rec y z) := by
  cases z <;> first | (exact absurd rfl hz) | rfl

/-- `__eo_list_concat_rec` of a proper list onto a non-`Stuck` list is non-`Stuck`. -/
theorem concat_rec_ne_stuck :
    ∀ L1 L2 : Term, IsElemList L1 -> L2 ≠ Term.Stuck ->
      __eo_list_concat_rec L1 L2 ≠ Term.Stuck := by
  intro L1 L2
  induction L1, L2 using __eo_list_concat_rec.induct with
  | case1 z => intro hL1 _; exact absurd hL1 (by simp [IsElemList])
  | case2 t ht => intro _ hL2; exact absurd rfl hL2
  | case3 f x y z hz ih =>
      intro hL1 hL2
      have hb : IsElemList y := hL1.2.2
      have hTail : __eo_list_concat_rec y z ≠ Term.Stuck := ih hb hL2
      rw [concat_rec_cons f x y z hL2, mk_apply_of_ne_stuck (by simp) hTail]
      simp
  | case4 nil z hns hzs hncons =>
      intro hL1 hL2
      have hEq : __eo_list_concat_rec nil z = z := by
        unfold __eo_list_concat_rec
        split <;> simp_all
      rw [hEq]; exact hL2

/-- `listLookup` distributes over `__eo_list_concat_rec` for a proper left list. -/
theorem listLookup_concat
    (M : SmtModel) (v : SmtValue) :
    ∀ L1 L2 : Term,
      IsElemList L1 -> L2 ≠ Term.Stuck ->
      listLookup M (__eo_list_concat_rec L1 L2) v =
        native_ite (native_veq (listLookup M L1 v) (SmtValue.Boolean true))
          (SmtValue.Boolean true) (listLookup M L2 v) := by
  intro L1 L2
  induction L1, L2 using __eo_list_concat_rec.induct with
  | case1 z => intro hL1 _; exact absurd hL1 (by simp [IsElemList])
  | case2 t ht => intro _ hL2; exact absurd rfl hL2
  | case3 f x y z hz ih =>
      intro hL1 hL2
      have hb : IsElemList y := hL1.2.2
      have hTail : __eo_list_concat_rec y z ≠ Term.Stuck :=
        concat_rec_ne_stuck y z hb hL2
      rw [concat_rec_cons f x y z hL2, mk_apply_of_ne_stuck (by simp) hTail,
        listLookup_cons, ih hb hL2, listLookup_cons]
      cases h : native_veq (__smtx_model_eval M (__eo_to_smt x)) v <;>
        simp [native_ite, native_veq]
  | case4 nil z hns hzs hncons =>
      intro hL1 hL2
      have hEq : __eo_list_concat_rec nil z = z := by
        unfold __eo_list_concat_rec
        split <;> simp_all
      have hLnil : listLookup M nil v = SmtValue.Boolean false := by
        unfold listLookup
        split <;> simp_all
      rw [hEq, hLnil]
      simp [native_ite, native_veq]

/-! ### Normal-form lookup equals listLookup -/

/-- For a union-of-singletons normal form `nf` (one on which `__set_union_to_list`
succeeds), the model lookup of `nf`'s set value at `v` equals `listLookup` of the
element list of `nf`. -/
theorem model_eval_singleton (M : SmtModel) (e : Term) :
    __smtx_model_eval M (__eo_to_smt ((Term.UOp UserOp.set_singleton).Apply e)) =
      SmtValue.Set (SmtMap.cons (__smtx_model_eval M (__eo_to_smt e))
        (SmtValue.Boolean true)
        (SmtMap.default (__smtx_typeof_value (__smtx_model_eval M (__eo_to_smt e)))
          (SmtValue.Boolean false))) := by
  show __smtx_model_eval M (SmtTerm.set_singleton (__eo_to_smt e)) = _
  simp [__smtx_model_eval, __smtx_model_eval_set_singleton]

theorem model_eval_union_eq (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.set_union a b) =
      __smtx_set_union (__smtx_model_eval M a) (__smtx_model_eval M b) := by
  simp [__smtx_model_eval, __smtx_model_eval_set_union]

theorem model_eval_inter_eq (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.set_inter a b) =
      __smtx_set_inter (__smtx_model_eval M a) (__smtx_model_eval M b) := by
  simp [__smtx_model_eval, __smtx_model_eval_set_inter]

theorem model_eval_minus_eq (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.set_minus a b) =
      __smtx_set_minus (__smtx_model_eval M a) (__smtx_model_eval M b) := by
  simp [__smtx_model_eval, __smtx_model_eval_set_minus]

theorem set_nf_lookup
    (M : SmtModel) (hM : model_wf M) :
    ∀ (nf : Term) (m : SmtMap) (v : SmtValue),
      __set_union_to_list nf ≠ Term.Stuck ->
      RuleProofs.eo_has_smt_translation nf ->
      __smtx_model_eval M (__eo_to_smt nf) = SmtValue.Set m ->
      __smtx_map_lookup m v = listLookup M (__set_union_to_list nf) v := by
  intro nf
  induction nf using __set_union_to_list.induct with
  | case1 e t ih =>
      intro m v hNS hTrans hEval
      have hsutlt : __set_union_to_list t ≠ Term.Stuck := by
        intro hSt
        apply hNS
        show __eo_mk_apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) e)
            (__set_union_to_list t) = Term.Stuck
        rw [hSt]; rfl
      unfold RuleProofs.eo_has_smt_translation at hTrans
      have hSU : __eo_to_smt
          (((Term.UOp UserOp.set_union).Apply
            ((Term.UOp UserOp.set_singleton).Apply e)).Apply t)
          = SmtTerm.set_union
            (__eo_to_smt ((Term.UOp UserOp.set_singleton).Apply e)) (__eo_to_smt t) := rfl
      rw [hSU] at hTrans hEval
      obtain ⟨A, hAse, hAt⟩ := set_binop_args_of_non_none (op := SmtTerm.set_union)
        (typeof_set_union_eq _ _) hTrans
      have hTransSe : RuleProofs.eo_has_smt_translation
          ((Term.UOp UserOp.set_singleton).Apply e) := by
        unfold RuleProofs.eo_has_smt_translation; rw [hAse]; simp
      have hTransT : RuleProofs.eo_has_smt_translation t := by
        unfold RuleProofs.eo_has_smt_translation; rw [hAt]; simp
      obtain ⟨m1, hm1eval, hm1can, hm1ty, hm1def⟩ :=
        set_value_facts M hM _ A hTransSe hAse
      obtain ⟨mt, hmteval, hmtcan, hmtty, hmtdef⟩ := set_value_facts M hM t A hTransT hAt
      have hm1cons : m1 = SmtMap.cons (__smtx_model_eval M (__eo_to_smt e))
          (SmtValue.Boolean true)
          (SmtMap.default (__smtx_typeof_value (__smtx_model_eval M (__eo_to_smt e)))
            (SmtValue.Boolean false)) := by
        rw [model_eval_singleton M e] at hm1eval
        injection hm1eval with h; exact h.symm
      have hModelU :
          __smtx_set_union (SmtValue.Set m1) (SmtValue.Set mt) = SmtValue.Set m := by
        rw [← hm1eval, ← hmteval, ← model_eval_union_eq]; exact hEval
      rw [__smtx_set_union] at hModelU
      injection hModelU with hmeq
      rw [← hmeq, set_union_lookup m1 mt A v hm1ty hmtty hm1can hmtcan hm1def, hm1cons]
      have hLook1 : __smtx_map_lookup
          (SmtMap.cons (__smtx_model_eval M (__eo_to_smt e)) (SmtValue.Boolean true)
            (SmtMap.default
              (__smtx_typeof_value (__smtx_model_eval M (__eo_to_smt e)))
              (SmtValue.Boolean false))) v
          = native_ite (native_veq (__smtx_model_eval M (__eo_to_smt e)) v)
            (SmtValue.Boolean true) (SmtValue.Boolean false) := by
        simp [__smtx_map_lookup]
      rw [hLook1]
      have hLL : listLookup M
          (__set_union_to_list (((Term.UOp UserOp.set_union).Apply
            ((Term.UOp UserOp.set_singleton).Apply e)).Apply t)) v
          = native_ite (native_veq (__smtx_model_eval M (__eo_to_smt e)) v)
            (SmtValue.Boolean true) (listLookup M (__set_union_to_list t) v) := by
        rw [show __set_union_to_list (((Term.UOp UserOp.set_union).Apply
              ((Term.UOp UserOp.set_singleton).Apply e)).Apply t)
            = __eo_mk_apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) e)
              (__set_union_to_list t) from rfl,
          mk_apply_of_ne_stuck (by simp) hsutlt, listLookup_cons]
      rw [hLL, ← ih mt v hsutlt hTransT hmteval]
      cases hvev : native_veq (__smtx_model_eval M (__eo_to_smt e)) v <;>
        simp [native_ite, native_veq]
  | case2 T =>
      intro m v hNS hTrans hEval
      unfold RuleProofs.eo_has_smt_translation at hTrans
      by_cases hA : __eo_to_smt_type T = SmtType.None
      · exfalso; apply hTrans
        show __smtx_typeof (__eo_to_smt_set_empty
          (__eo_to_smt_type ((Term.UOp UserOp.Set).Apply T))) = SmtType.None
        have hg : __eo_to_smt_type ((Term.UOp UserOp.Set).Apply T) = SmtType.None := by
          show __smtx_typeof_guard (__eo_to_smt_type T)
            (SmtType.Set (__eo_to_smt_type T)) = SmtType.None
          rw [hA]; rfl
        rw [hg]; simp [__eo_to_smt_set_empty]
      · have hType : __eo_to_smt_type ((Term.UOp UserOp.Set).Apply T) =
            SmtType.Set (__eo_to_smt_type T) :=
          TranslationProofs.smtx_typeof_guard_of_non_none _ _ hA
        have hEval2 : SmtValue.Set m =
            SmtValue.Set (SmtMap.default (__eo_to_smt_type T) (SmtValue.Boolean false)) := by
          rw [← hEval]
          show __smtx_model_eval M (__eo_to_smt_set_empty
            (__eo_to_smt_type ((Term.UOp UserOp.Set).Apply T))) = _
          rw [hType]; simp [__eo_to_smt_set_empty, __smtx_model_eval]
        injection hEval2 with hmeq
        rw [hmeq]; rfl
  | case3 e =>
      intro m v hNS hTrans hEval
      rw [model_eval_singleton M e] at hEval
      injection hEval with hmeq
      subst hmeq
      have hnilne :
          __eo_nil (Term.UOp UserOp._at__at_TypedList_cons) (__eo_typeof e) ≠ Term.Stuck := by
        intro hSt
        apply hNS
        show __eo_mk_apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) e)
            (__eo_nil (Term.UOp UserOp._at__at_TypedList_cons) (__eo_typeof e)) = Term.Stuck
        rw [hSt]; rfl
      have hnilform :
          __eo_nil (Term.UOp UserOp._at__at_TypedList_cons) (__eo_typeof e) =
            Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) (__eo_typeof e) := by
        cases h : __eo_typeof e <;>
          simp_all [__eo_nil, __eo_nil__at__at_TypedList_cons]
      rw [show __set_union_to_list ((Term.UOp UserOp.set_singleton).Apply e)
          = __eo_mk_apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) e)
            (__eo_nil (Term.UOp UserOp._at__at_TypedList_cons) (__eo_typeof e)) from rfl,
        hnilform, mk_apply_of_ne_stuck (by simp) (by simp),
        listLookup_cons,
        show listLookup M (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil)
          (__eo_typeof e)) v = SmtValue.Boolean false from rfl]
      have hLook1 : __smtx_map_lookup
          (SmtMap.cons (__smtx_model_eval M (__eo_to_smt e)) (SmtValue.Boolean true)
            (SmtMap.default
              (__smtx_typeof_value (__smtx_model_eval M (__eo_to_smt e)))
              (SmtValue.Boolean false))) v
          = native_ite (native_veq (__smtx_model_eval M (__eo_to_smt e)) v)
            (SmtValue.Boolean true) (SmtValue.Boolean false) := by
        simp [__smtx_map_lookup]
      rw [hLook1]
  | case4 g hc1 hc2 hc3 =>
      intro m v hNS _ _
      exact absurd (by unfold __set_union_to_list; split <;> simp_all) hNS

/-! ### setof preserves membership, meq implies membership equality -/

/-- `__eo_eq` of two non-`Stuck` terms is the Boolean of their decidable equality. -/
theorem eo_eq_val (a b : Term) (ha : a ≠ Term.Stuck) (hb : b ≠ Term.Stuck) :
    __eo_eq a b = Term.Boolean (native_teq b a) := by
  unfold __eo_eq; split <;> simp_all

theorem prepend_if_keep (f x res : Term)
    (hf : f ≠ Term.Stuck) (hx : x ≠ Term.Stuck) (hres : res ≠ Term.Stuck) :
    __eo_prepend_if (Term.Boolean true) f x res = Term.Apply (Term.Apply f x) res := by
  unfold __eo_prepend_if; split <;> simp_all

theorem prepend_if_drop (f x res : Term)
    (hf : f ≠ Term.Stuck) (hx : x ≠ Term.Stuck) (hres : res ≠ Term.Stuck) :
    __eo_prepend_if (Term.Boolean false) f x res = res := by
  unfold __eo_prepend_if; split <;> simp_all

theorem erase_all_rec_cons (f x y z : Term) (hz : z ≠ Term.Stuck) :
    __eo_list_erase_all_rec (Term.Apply (Term.Apply f x) y) z =
      __eo_prepend_if (__eo_not (__eo_eq z x)) f x (__eo_list_erase_all_rec y z) := by
  cases z <;> first | (exact absurd rfl hz) | rfl

/-- `__eo_list_erase_all_rec` preserves the element-list invariant. -/
theorem erase_all_isElemList :
    ∀ L z : Term, IsElemList L -> z ≠ Term.Stuck ->
      IsElemList (__eo_list_erase_all_rec L z) := by
  intro L z
  induction L, z using __eo_list_erase_all_rec.induct with
  | case1 z => intro hL _; exact absurd hL (by simp [IsElemList])
  | case2 t ht => intro _ hz; exact absurd rfl hz
  | case3 f x y z hz ih =>
      intro hL hzs
      obtain ⟨hf, hx, hy⟩ := hL
      have hTail : IsElemList (__eo_list_erase_all_rec y z) := ih hy hzs
      have hTailNS := isElemList_ne_stuck hTail
      rw [erase_all_rec_cons f x y z hzs, eo_eq_val z x hzs hx]
      cases hxz : native_teq x z
      · rw [show __eo_not (Term.Boolean false) = Term.Boolean true by decide,
          prepend_if_keep f x _ hf hx hTailNS]
        exact ⟨hf, hx, hTail⟩
      · rw [show __eo_not (Term.Boolean true) = Term.Boolean false by decide,
          prepend_if_drop f x _ hf hx hTailNS]
        exact hTail
  | case4 nil z hns hzs hncons =>
      intro hL _
      have hEq : __eo_list_erase_all_rec nil z = nil := by
        unfold __eo_list_erase_all_rec; split <;> simp_all
      rw [hEq]; exact hL

/-- Erasing all syntactic copies of `z` does not change membership of `v` when `v`
is not the model value of `z`. -/
theorem erase_all_mem (M : SmtModel) (v : SmtValue) :
    ∀ L z : Term, IsElemList L -> z ≠ Term.Stuck ->
      native_veq (__smtx_model_eval M (__eo_to_smt z)) v = false ->
      listLookup M (__eo_list_erase_all_rec L z) v = listLookup M L v := by
  intro L z
  induction L, z using __eo_list_erase_all_rec.induct with
  | case1 z => intro hL _ _; exact absurd hL (by simp [IsElemList])
  | case2 t ht => intro _ hz _; exact absurd rfl hz
  | case3 f x y z hz ih =>
      intro hL hzs hveq
      obtain ⟨hf, hx, hy⟩ := hL
      have hTail : IsElemList (__eo_list_erase_all_rec y z) :=
        erase_all_isElemList y z hy hzs
      have hTailNS := isElemList_ne_stuck hTail
      have ihm := ih hy hzs hveq
      rw [erase_all_rec_cons f x y z hzs, eo_eq_val z x hzs hx]
      cases hxz : native_teq x z
      · rw [show __eo_not (Term.Boolean false) = Term.Boolean true by decide,
          prepend_if_keep f x _ hf hx hTailNS, listLookup_cons, ihm, listLookup_cons]
      · rw [show __eo_not (Term.Boolean true) = Term.Boolean false by decide,
          prepend_if_drop f x _ hf hx hTailNS, ihm, listLookup_cons]
        have hxe : x = z := of_decide_eq_true hxz
        rw [hxe, hveq]; simp [native_ite]
  | case4 nil z hns hzs hncons =>
      intro hL _ _
      have hEq : __eo_list_erase_all_rec nil z = nil := by
        unfold __eo_list_erase_all_rec; split <;> simp_all
      rw [hEq]

end SetsEvalOpSupport
end

open Eo
open SmtEval
open Smtm

namespace SetsEvalOpSupport

theorem setof_rec_cons (f x y : Term) :
    __eo_list_setof_rec (Term.Apply (Term.Apply f x) y) =
      __eo_mk_apply (Term.Apply f x)
        (__eo_list_erase_all_rec (__eo_list_setof_rec y) x) := rfl

theorem eo_ite_true (yes no : Term) : __eo_ite (Term.Boolean true) yes no = yes := rfl

theorem eo_ite_false (yes no : Term) : __eo_ite (Term.Boolean false) yes no = no := rfl

theorem listLookup_nil_list (M : SmtModel) (v : SmtValue) :
    listLookup M Term.__eo_List_nil v = SmtValue.Boolean false := rfl

theorem getelem_cons (f x y : Term) :
    __eo_get_elements_rec (Term.Apply (Term.Apply f x) y) =
      __eo_mk_apply (Term.Apply Term.__eo_List_cons x) (__eo_get_elements_rec y) := rfl

end SetsEvalOpSupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace SetsEvalOpSupport

open SetsMemberSupport

/-- `__eo_list_setof_rec` preserves the element-list invariant. -/
theorem setof_rec_isElemList :
    ∀ L : Term, IsElemList L -> IsElemList (__eo_list_setof_rec L) := by
  intro L
  induction L using __eo_list_setof_rec.induct with
  | case1 => intro hL; exact absurd hL (by simp [IsElemList])
  | case2 f x y ih =>
      intro hL
      obtain ⟨hf, hx, hy⟩ := hL
      have hSy := ih hy
      have hEr := erase_all_isElemList (__eo_list_setof_rec y) x hSy hx
      have hErNS := isElemList_ne_stuck hEr
      rw [setof_rec_cons, mk_apply_of_ne_stuck (by simp) hErNS]
      exact ⟨hf, hx, hEr⟩
  | case3 nil hns hncons =>
      intro hL
      have hEq : __eo_list_setof_rec nil = nil := by
        unfold __eo_list_setof_rec; split <;> simp_all
      rw [hEq]; exact hL

theorem listLookup_setof
    (M : SmtModel) (v : SmtValue) :
    ∀ L : Term,
      IsElemList L ->
      listLookup M (__eo_list_setof_rec L) v = listLookup M L v := by
  intro L
  induction L using __eo_list_setof_rec.induct with
  | case1 => intro hL; exact absurd hL (by simp [IsElemList])
  | case2 f x y ih =>
      intro hL
      obtain ⟨hf, hx, hy⟩ := hL
      have hSy := setof_rec_isElemList y hy
      have hEr := erase_all_isElemList (__eo_list_setof_rec y) x hSy hx
      have hErNS := isElemList_ne_stuck hEr
      have ihm := ih hy
      rw [setof_rec_cons, mk_apply_of_ne_stuck (by simp) hErNS, listLookup_cons,
        listLookup_cons]
      cases hxv : native_veq (__smtx_model_eval M (__eo_to_smt x)) v
      · simp only [native_ite]
        rw [erase_all_mem M v (__eo_list_setof_rec y) x hSy hx hxv, ihm]
      · simp [native_ite]
  | case3 nil hns hncons =>
      intro hL
      have hEq : __eo_list_setof_rec nil = nil := by
        unfold __eo_list_setof_rec; split <;> simp_all
      rw [hEq]

/-! #### `__eo_requires` / `__eo_and` / `__eo_ite` reductions -/

theorem req_arg_eq {x y z : Term} (h : __eo_requires x y z ≠ Term.Stuck) : x = y := by
  by_cases hxy : x = y
  · exact hxy
  · exact absurd (by simp [__eo_requires, native_teq, native_ite, hxy]) h

theorem req_left_ne {x y z : Term} (h : __eo_requires x y z ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx; subst hx
  have hxy : Term.Stuck = y := req_arg_eq h
  subst hxy
  simp [__eo_requires, native_teq, native_ite, native_not, SmtEval.native_not] at h

theorem req_result {x y z : Term} (h : __eo_requires x y z ≠ Term.Stuck) :
    __eo_requires x y z = z := by
  have hxy : x = y := req_arg_eq h
  have hx : x ≠ Term.Stuck := req_left_ne h
  subst hxy
  cases x <;> simp [__eo_requires, native_teq, native_ite, native_not,
    SmtEval.native_not] at hx ⊢

theorem eo_and_eq_true {p q : Term} (h : __eo_and p q = Term.Boolean true) :
    p = Term.Boolean true ∧ q = Term.Boolean true := by
  cases p <;> cases q <;>
    simp_all [__eo_and, native_and, __eo_requires, native_ite, native_teq,
      native_not, SmtEval.native_not, Bool.and_eq_true] <;>
    split at h <;> simp_all

/-! #### `__eo_list_erase_rec` lemmas -/

theorem erase_rec_cons (f w y t : Term) (ht : t ≠ Term.Stuck) :
    __eo_list_erase_rec (Term.Apply (Term.Apply f w) y) t =
      __eo_ite (__eo_eq w t) y
        (__eo_mk_apply (Term.Apply f w) (__eo_list_erase_rec y t)) := by
  cases t <;> first | (exact absurd rfl ht) | rfl

theorem erase_rec_isElemList :
    ∀ L t : Term, IsElemList L -> t ≠ Term.Stuck ->
      IsElemList (__eo_list_erase_rec L t) := by
  intro L t
  induction L, t using __eo_list_erase_rec.induct with
  | case1 z => intro hL _; exact absurd hL (by simp [IsElemList])
  | case2 s hs => intro _ ht; exact absurd rfl ht
  | case3 f w y t ht ih =>
      intro hL hts
      obtain ⟨hf, hw, hy⟩ := hL
      have hTail := ih hy hts
      have hTailNS := isElemList_ne_stuck hTail
      rw [erase_rec_cons f w y t hts, eo_eq_val w t hw hts]
      cases htw : native_teq t w
      · rw [eo_ite_false, mk_apply_of_ne_stuck (by simp) hTailNS]
        exact ⟨hf, hw, hTail⟩
      · rw [eo_ite_true]; exact hy
  | case4 nil t hns hts hncons =>
      intro hL _
      have hEq : __eo_list_erase_rec nil t = nil := by
        unfold __eo_list_erase_rec; split <;> simp_all
      rw [hEq]; exact hL

theorem erase_mono (M : SmtModel) (v : SmtValue) :
    ∀ L t : Term, IsElemList L -> t ≠ Term.Stuck ->
      listLookup M (__eo_list_erase_rec L t) v = SmtValue.Boolean true ->
      listLookup M L v = SmtValue.Boolean true := by
  intro L t
  induction L, t using __eo_list_erase_rec.induct with
  | case1 z => intro hL _ _; exact absurd hL (by simp [IsElemList])
  | case2 s hs => intro _ ht _; exact absurd rfl ht
  | case3 f w y t ht ih =>
      intro hL hts hh
      obtain ⟨hf, hw, hy⟩ := hL
      have hTail := erase_rec_isElemList y t hy hts
      have hTailNS := isElemList_ne_stuck hTail
      rw [erase_rec_cons f w y t hts, eo_eq_val w t hw hts] at hh
      rw [listLookup_cons]
      cases htw : native_teq t w
      · rw [htw, eo_ite_false, mk_apply_of_ne_stuck (by simp) hTailNS,
          listLookup_cons] at hh
        cases hvw : native_veq (__smtx_model_eval M (__eo_to_smt w)) v
        · rw [hvw] at hh
          simp only [native_ite] at hh ⊢
          exact ih hy hts hh
        · simp [native_ite]
      · rw [htw, eo_ite_true] at hh
        cases hvw : native_veq (__smtx_model_eval M (__eo_to_smt w)) v
        · simp only [native_ite]; exact hh
        · simp [native_ite]
  | case4 nil t hns hts hncons =>
      intro hL _ hh
      have hEq : __eo_list_erase_rec nil t = nil := by
        unfold __eo_list_erase_rec; split <;> simp_all
      rw [hEq] at hh; exact hh

theorem erase_present (M : SmtModel) :
    ∀ L t : Term, IsElemList L -> t ≠ Term.Stuck ->
      __eo_list_erase_rec L t ≠ L ->
      listLookup M L (__smtx_model_eval M (__eo_to_smt t)) = SmtValue.Boolean true := by
  intro L t
  induction L, t using __eo_list_erase_rec.induct with
  | case1 z => intro hL _ _; exact absurd hL (by simp [IsElemList])
  | case2 s hs => intro _ ht _; exact absurd rfl ht
  | case3 f w y t ht ih =>
      intro hL hts hne
      obtain ⟨hf, hw, hy⟩ := hL
      have hTail := erase_rec_isElemList y t hy hts
      have hTailNS := isElemList_ne_stuck hTail
      rw [erase_rec_cons f w y t hts, eo_eq_val w t hw hts] at hne
      rw [listLookup_cons]
      cases htw : native_teq t w
      · rw [htw] at hne
        rw [eo_ite_false, mk_apply_of_ne_stuck (by simp) hTailNS] at hne
        have hne' : __eo_list_erase_rec y t ≠ y := by
          intro hEqyt; exact hne (by rw [hEqyt])
        have hyp := ih hy hts hne'
        rw [hyp]
        cases native_veq (__smtx_model_eval M (__eo_to_smt w))
            (__smtx_model_eval M (__eo_to_smt t)) <;> simp [native_ite]
      · have htwe : t = w := of_decide_eq_true htw
        rw [htwe]; simp [native_ite, native_veq]
  | case4 nil t hns hts hncons =>
      intro hL _ hne
      have hEq : __eo_list_erase_rec nil t = nil := by
        unfold __eo_list_erase_rec; split <;> simp_all
      exact absurd hEq hne

/-! #### `__eo_list_minclude_rec` lemmas -/

theorem minclude_rec_cons (y x z : Term) (hy : y ≠ Term.Stuck) :
    __eo_list_minclude_rec y (Term.Apply (Term.Apply Term.__eo_List_cons x) z)
        (Term.Boolean true) =
      __eo_list_minclude_rec (__eo_list_erase_rec y x) z
        (__eo_not (__eo_eq (__eo_list_erase_rec y x) y)) := by
  cases y <;> first | (exact absurd rfl hy) | rfl

theorem minclude_rec_false (y z : Term) (hy : y ≠ Term.Stuck) (hz : z ≠ Term.Stuck) :
    __eo_list_minclude_rec y z (Term.Boolean false) = Term.Boolean false := by
  cases y <;> cases z <;>
    first | (exact absurd rfl hy) | (exact absurd rfl hz) | rfl

theorem minclude_mem (M : SmtModel) (v : SmtValue) :
    ∀ Y Z g : Term,
      __eo_list_minclude_rec Y Z g = Term.Boolean true ->
      IsElemList Y -> IsElemList Z ->
      listLookup M Z v = SmtValue.Boolean true ->
      listLookup M Y v = SmtValue.Boolean true := by
  intro Y Z g
  induction Y, Z, g using __eo_list_minclude_rec.induct with
  | case1 t x => intro _ hY _ _; exact absurd hY (by simp [IsElemList])
  | case2 y x hy => intro _ _ hZ _; exact absurd hZ (by simp [IsElemList])
  | case3 y z hy hz => intro h _ _ _; rw [minclude_rec_false y z hy hz] at h; cases h
  | case4 y x z hy v0 ih =>
      intro h hY hZ hv
      obtain ⟨hxf, hx, hz⟩ := hZ
      have hEr := erase_rec_isElemList y x hY hx
      have hErNS := isElemList_ne_stuck hEr
      have hyNS := isElemList_ne_stuck hY
      have hzNS := isElemList_ne_stuck hz
      rw [minclude_rec_cons y x z hyNS] at h
      by_cases heq : __eo_list_erase_rec y x = y
      · -- erase removed nothing: guard is false, contradicting h
        exfalso
        rw [heq] at h
        rw [eo_eq_val y y hyNS hyNS] at h
        have hyy : native_teq y y = true := by simp [native_teq]
        rw [hyy] at h
        rw [show __eo_not (Term.Boolean true) = Term.Boolean false from rfl] at h
        rw [minclude_rec_false y z hyNS hzNS] at h
        cases h
      · rw [listLookup_cons] at hv
        cases hvx : native_veq (__smtx_model_eval M (__eo_to_smt x)) v
        · -- v ≠ eval x: membership comes from z
          rw [hvx] at hv
          simp only [native_ite] at hv
          have hzmem := ih h hEr hz hv
          exact erase_mono M v y x hY hx hzmem
        · -- v = eval x: x present in y (erase changed y)
          have hvxe : __smtx_model_eval M (__eo_to_smt x) = v :=
            eq_of_native_veq_true hvx
          have hp := erase_present M y x hY hx heq
          rw [hvxe] at hp
          exact hp
  | case5 y hy => intro _ _ _ hv; rw [listLookup_nil_list] at hv; cases hv
  | case6 t x g hx hg ht hcons hnil =>
      intro h _ _ _
      exfalso
      have hStuck : __eo_list_minclude_rec x t g = Term.Stuck := by
        unfold __eo_list_minclude_rec; split <;> simp_all
      rw [hStuck] at h; cases h

/-! #### `__eo_get_elements_rec` lemmas -/

theorem getelem_isElemList :
    ∀ L : Term, IsElemList L -> IsElemList (__eo_get_elements_rec L) := by
  intro L
  induction L using __eo_get_elements_rec.induct with
  | case1 => intro hL; exact absurd hL (by simp [IsElemList])
  | case2 f x y ih =>
      intro hL
      obtain ⟨hf, hx, hy⟩ := hL
      have hTail := ih hy
      have hTailNS := isElemList_ne_stuck hTail
      rw [getelem_cons, mk_apply_of_ne_stuck (by simp) hTailNS]
      exact ⟨by simp, hx, hTail⟩
  | case3 nil hns hncons =>
      intro hL
      have hEq : __eo_get_elements_rec nil = Term.__eo_List_nil := by
        unfold __eo_get_elements_rec; split <;> simp_all
      rw [hEq]; trivial

theorem getelem_mem (M : SmtModel) (v : SmtValue) :
    ∀ L : Term, IsElemList L ->
      listLookup M (__eo_get_elements_rec L) v = listLookup M L v := by
  intro L
  induction L using __eo_get_elements_rec.induct with
  | case1 => intro hL; exact absurd hL (by simp [IsElemList])
  | case2 f x y ih =>
      intro hL
      obtain ⟨hf, hx, hy⟩ := hL
      have hTail := getelem_isElemList y hy
      have hTailNS := isElemList_ne_stuck hTail
      rw [getelem_cons, mk_apply_of_ne_stuck (by simp) hTailNS, listLookup_cons,
        ih hy, listLookup_cons]
  | case3 nil hns hncons =>
      intro hL
      have hEq : __eo_get_elements_rec nil = Term.__eo_List_nil := by
        unfold __eo_get_elements_rec; split <;> simp_all
      have hLnil : listLookup M nil v = SmtValue.Boolean false := by
        unfold listLookup; split <;> simp_all
      rw [hEq, hLnil, listLookup_nil_list]

/-! #### listLookup is Boolean-valued, and the meq membership theorem -/

theorem listLookup_isBool (M : SmtModel) :
    ∀ (L : Term) (v : SmtValue), ∃ b, listLookup M L v = SmtValue.Boolean b := by
  intro L v
  induction L, v using listLookup.induct with
  | case1 a x y v ih =>
      rw [listLookup_cons]
      cases native_veq (__smtx_model_eval M (__eo_to_smt x)) v
      · simpa [native_ite] using ih
      · exact ⟨true, by simp [native_ite]⟩
  | case2 t v hnc =>
      refine ⟨false, ?_⟩
      unfold listLookup; split
      · next a x y => exact absurd rfl (hnc a x y)
      · rfl

/-- If `__eo_list_meq` on two element lists evaluates to `true`, their `listLookup`
membership characteristic values agree everywhere. -/
theorem listLookup_meq
    (M : SmtModel) (X Y : Term) (v : SmtValue)
    (hX : IsElemList X) (hY : IsElemList Y)
    (hMeq : __eo_list_meq (Term.UOp UserOp._at__at_TypedList_cons) X Y =
      Term.Boolean true) :
    listLookup M X v = listLookup M Y v := by
  have hgeXel : IsElemList (__eo_get_elements_rec X) := getelem_isElemList X hX
  have hgeYel : IsElemList (__eo_get_elements_rec Y) := getelem_isElemList Y hY
  -- Unfold meq into the conjunction of the two minclude checks.
  have hMeq' : __eo_and
      (__eo_list_minclude_rec
        (__eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) X)
          (Term.Boolean true) (__eo_get_elements_rec X))
        (__eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) Y)
          (Term.Boolean true) (__eo_get_elements_rec Y))
        (Term.Boolean true))
      (__eo_list_minclude_rec
        (__eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) Y)
          (Term.Boolean true) (__eo_get_elements_rec Y))
        (__eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) X)
          (Term.Boolean true) (__eo_get_elements_rec X))
        (Term.Boolean true)) = Term.Boolean true := by
    simpa [__eo_list_meq] using hMeq
  obtain ⟨hXY, hYX⟩ := eo_and_eq_true hMeq'
  -- The minclude checks force the `is_list` requirements to hold.
  have hrXne :
      __eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) X)
        (Term.Boolean true) (__eo_get_elements_rec X) ≠ Term.Stuck := by
    intro hStuck; rw [hStuck] at hXY; simp [__eo_list_minclude_rec] at hXY
  have hrYne :
      __eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) Y)
        (Term.Boolean true) (__eo_get_elements_rec Y) ≠ Term.Stuck := by
    intro hStuck; rw [hStuck] at hYX; simp [__eo_list_minclude_rec] at hYX
  rw [req_result hrXne, req_result hrYne] at hXY hYX
  -- Membership inclusions both ways.
  have hsubXY : listLookup M (__eo_get_elements_rec Y) v = SmtValue.Boolean true ->
      listLookup M (__eo_get_elements_rec X) v = SmtValue.Boolean true :=
    fun hh => minclude_mem M v (__eo_get_elements_rec X) (__eo_get_elements_rec Y)
      (Term.Boolean true) hXY hgeXel hgeYel hh
  have hsubYX : listLookup M (__eo_get_elements_rec X) v = SmtValue.Boolean true ->
      listLookup M (__eo_get_elements_rec Y) v = SmtValue.Boolean true :=
    fun hh => minclude_mem M v (__eo_get_elements_rec Y) (__eo_get_elements_rec X)
      (Term.Boolean true) hYX hgeYel hgeXel hh
  rw [← getelem_mem M v X hX, ← getelem_mem M v Y hY]
  obtain ⟨bX, hbX⟩ := listLookup_isBool M (__eo_get_elements_rec X) v
  obtain ⟨bY, hbY⟩ := listLookup_isBool M (__eo_get_elements_rec Y) v
  rw [hbX, hbY]
  cases bX <;> cases bY
  · rfl
  · exact absurd (hsubXY hbY) (by rw [hbX]; decide)
  · exact absurd (hsubYX hbX) (by rw [hbY]; decide)
  · rfl

/-! ### Typed-cons-list machinery and the union-case assembly -/

theorem set_singleton_typeof_none {x : SmtTerm} (h : __smtx_typeof x = SmtType.None) :
    __smtx_typeof (SmtTerm.set_singleton x) = SmtType.None := by
  rw [smtx_typeof_set_singleton_term_eq, h, __smtx_typeof_guard_wf]
  simp [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
    native_and, native_ite]

/-- The argument of a translatable `set.singleton` is itself translatable. -/
theorem singleton_elem_trans {e : Term}
    (h : RuleProofs.eo_has_smt_translation ((Term.UOp UserOp.set_singleton).Apply e)) :
    RuleProofs.eo_has_smt_translation e := by
  unfold RuleProofs.eo_has_smt_translation at h ⊢
  intro hNone
  exact h (set_singleton_typeof_none hNone)

/-- A `@@TypedList` with `@@cons` spine heads and non-`Stuck` elements. -/
def IsTL : Term -> Prop
  | Term.Apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) x) y =>
      x ≠ Term.Stuck ∧ IsTL y
  | Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) _ => True
  | _ => False

theorem isTL_ne_stuck {L : Term} (h : IsTL L) : L ≠ Term.Stuck := by
  intro h0; rw [h0] at h; exact h

theorem isTL_isElemList : ∀ L : Term, IsTL L -> IsElemList L := by
  intro L
  induction L using IsTL.induct with
  | case1 x y ih => intro hTL; obtain ⟨hx, hy⟩ := hTL; exact ⟨by simp, hx, ih hy⟩
  | case2 a => intro _; trivial
  | case3 t hc1 hc2 => intro hTL; exact absurd hTL (by
      cases t <;> simp_all [IsTL])

theorem isTL_get_nil_ne_stuck : ∀ L : Term, IsTL L ->
    __eo_get_nil_rec (Term.UOp UserOp._at__at_TypedList_cons) L ≠ Term.Stuck := by
  intro L
  induction L using IsTL.induct with
  | case1 x y ih =>
      intro hTL
      obtain ⟨hx, hy⟩ := hTL
      rw [show __eo_get_nil_rec (Term.UOp UserOp._at__at_TypedList_cons)
          (((Term.UOp UserOp._at__at_TypedList_cons).Apply x).Apply y) =
          __eo_get_nil_rec (Term.UOp UserOp._at__at_TypedList_cons) y from by
        simp [__eo_get_nil_rec, __eo_requires, native_teq, native_ite,
          native_not, SmtEval.native_not]]
      exact ih hy
  | case2 a =>
      intro _
      simp [__eo_get_nil_rec, __eo_is_list_nil, __eo_is_list_nil__at__at_TypedList_cons,
        __eo_requires, native_teq, native_ite, native_not, SmtEval.native_not]
  | case3 t hc1 hc2 => intro hTL; exact absurd hTL (by cases t <;> simp_all [IsTL])

theorem isTL_is_list (L : Term) (h : IsTL L) :
    __eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) L = Term.Boolean true := by
  have hne := isTL_get_nil_ne_stuck L h
  have hLne : L ≠ Term.Stuck := isTL_ne_stuck h
  rw [show __eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) L =
      __eo_is_ok (__eo_get_nil_rec (Term.UOp UserOp._at__at_TypedList_cons) L) from by
    cases L <;> simp_all [__eo_is_list]]
  unfold __eo_is_ok
  simp [native_teq, native_not, SmtEval.native_not, hne]

theorem req_tt (z : Term) : __eo_requires (Term.Boolean true) (Term.Boolean true) z = z := by
  simp [__eo_requires, native_teq, native_ite, native_not, SmtEval.native_not]

theorem isTL_sutl : ∀ nf : Term,
    RuleProofs.eo_has_smt_translation nf -> __set_union_to_list nf ≠ Term.Stuck ->
    IsTL (__set_union_to_list nf) := by
  intro nf
  induction nf using __set_union_to_list.induct with
  | case1 e t ih =>
      intro hTrans hNS
      have hsutlt : __set_union_to_list t ≠ Term.Stuck := by
        intro hSt; apply hNS
        show __eo_mk_apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) e)
            (__set_union_to_list t) = Term.Stuck
        rw [hSt]; rfl
      unfold RuleProofs.eo_has_smt_translation at hTrans
      have hSU : __eo_to_smt
          (((Term.UOp UserOp.set_union).Apply
            ((Term.UOp UserOp.set_singleton).Apply e)).Apply t)
          = SmtTerm.set_union
            (__eo_to_smt ((Term.UOp UserOp.set_singleton).Apply e)) (__eo_to_smt t) := rfl
      rw [hSU] at hTrans
      obtain ⟨A, hAse, hAt⟩ := set_binop_args_of_non_none (op := SmtTerm.set_union)
        (typeof_set_union_eq _ _) hTrans
      have hTransSe : RuleProofs.eo_has_smt_translation
          ((Term.UOp UserOp.set_singleton).Apply e) := by
        unfold RuleProofs.eo_has_smt_translation; rw [hAse]; simp
      have hTransT : RuleProofs.eo_has_smt_translation t := by
        unfold RuleProofs.eo_has_smt_translation; rw [hAt]; simp
      have he : e ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_smt_translation e (singleton_elem_trans hTransSe)
      rw [show __set_union_to_list (((Term.UOp UserOp.set_union).Apply
            ((Term.UOp UserOp.set_singleton).Apply e)).Apply t)
          = __eo_mk_apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) e)
            (__set_union_to_list t) from rfl,
        mk_apply_of_ne_stuck (by simp) hsutlt]
      exact ⟨he, ih hTransT hsutlt⟩
  | case2 T => intro _ _; trivial
  | case3 e =>
      intro hTrans hNS
      have he : e ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_smt_translation e (singleton_elem_trans hTrans)
      have hnilne :
          __eo_nil (Term.UOp UserOp._at__at_TypedList_cons) (__eo_typeof e) ≠ Term.Stuck := by
        intro hSt; apply hNS
        show __eo_mk_apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) e)
            (__eo_nil (Term.UOp UserOp._at__at_TypedList_cons) (__eo_typeof e)) = Term.Stuck
        rw [hSt]; rfl
      have hnilform :
          __eo_nil (Term.UOp UserOp._at__at_TypedList_cons) (__eo_typeof e) =
            Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) (__eo_typeof e) := by
        cases h : __eo_typeof e <;>
          simp_all [__eo_nil, __eo_nil__at__at_TypedList_cons]
      rw [show __set_union_to_list ((Term.UOp UserOp.set_singleton).Apply e)
          = __eo_mk_apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) e)
            (__eo_nil (Term.UOp UserOp._at__at_TypedList_cons) (__eo_typeof e)) from rfl,
        hnilform, mk_apply_of_ne_stuck (by simp) (by simp)]
      exact ⟨he, trivial⟩
  | case4 g hc1 hc2 hc3 =>
      intro _ hNS
      exact absurd (by unfold __set_union_to_list; split <;> simp_all) hNS

theorem isTL_concat_rec : ∀ L1 : Term, IsTL L1 -> ∀ L2 : Term, IsTL L2 ->
    IsTL (__eo_list_concat_rec L1 L2) := by
  intro L1
  induction L1 using IsTL.induct with
  | case1 x y ih =>
      intro hTL L2 hL2
      obtain ⟨hx, hy⟩ := hTL
      have hL2ne := isTL_ne_stuck hL2
      have hTail := ih hy L2 hL2
      rw [concat_rec_cons (Term.UOp UserOp._at__at_TypedList_cons) x y L2 hL2ne,
        mk_apply_of_ne_stuck (by simp) (isTL_ne_stuck hTail)]
      exact ⟨hx, hTail⟩
  | case2 a =>
      intro _ L2 hL2
      rw [show __eo_list_concat_rec (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) a) L2
          = L2 from by
        cases L2 <;> first | (exact absurd rfl (isTL_ne_stuck hL2)) | rfl]
      exact hL2
  | case3 t hc1 hc2 => intro hTL _ _; exact absurd hTL (by cases t <;> simp_all [IsTL])

theorem concat_rec_isElemList : ∀ L1 L2 : Term,
    IsElemList L1 -> IsElemList L2 -> IsElemList (__eo_list_concat_rec L1 L2) := by
  intro L1 L2
  induction L1, L2 using __eo_list_concat_rec.induct with
  | case1 z => intro hL1 _; exact absurd hL1 (by simp [IsElemList])
  | case2 t ht => intro _ hL2; exact absurd (isElemList_ne_stuck hL2) (by simp)
  | case3 f x y z hz ih =>
      intro hL1 hL2
      obtain ⟨hf, hx, hy⟩ := hL1
      have hTail := ih hy hL2
      rw [concat_rec_cons f x y z (isElemList_ne_stuck hL2),
        mk_apply_of_ne_stuck (by simp) (isElemList_ne_stuck hTail)]
      exact ⟨hf, hx, hTail⟩
  | case4 nil z hns hzs hncons =>
      intro hL1 hL2
      rw [show __eo_list_concat_rec nil z = z from by
        unfold __eo_list_concat_rec; split <;> simp_all]
      exact hL2

theorem is_list_cons_ne_stuck {L : Term}
    (h : __eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) L = Term.Boolean true) :
    L ≠ Term.Stuck := by
  intro h0; rw [h0] at h; simp [__eo_is_list] at h

theorem concat_parts {a b : Term}
    (h : __eo_list_concat (Term.UOp UserOp._at__at_TypedList_cons) a b ≠ Term.Stuck) :
    __eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) a = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) b = Term.Boolean true ∧
      __eo_list_concat (Term.UOp UserOp._at__at_TypedList_cons) a b =
        __eo_list_concat_rec a b := by
  have hOuter : __eo_list_concat (Term.UOp UserOp._at__at_TypedList_cons) a b =
      __eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) a)
        (Term.Boolean true)
        (__eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) b)
          (Term.Boolean true) (__eo_list_concat_rec a b)) := rfl
  rw [hOuter] at h ⊢
  have hListA := req_arg_eq h
  have hInner := req_result h
  rw [hInner] at h ⊢
  exact ⟨hListA, req_arg_eq h, req_result h⟩

theorem setof_parts {L : Term}
    (h : __eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons) L ≠ Term.Stuck) :
    __eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) L = Term.Boolean true ∧
      __eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons) L =
        __eo_list_setof_rec L := by
  have hOuter : __eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons) L =
      __eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) L)
        (Term.Boolean true) (__eo_list_setof_rec L) := rfl
  rw [hOuter] at h ⊢
  exact ⟨req_arg_eq h, req_result h⟩

/-! ### Intersection / difference support -/

theorem map_canonical_default (A : SmtType) :
    __smtx_map_canonical (SmtMap.default A (SmtValue.Boolean false)) = true := by
  simp only [__smtx_map_canonical, __smtx_map_default_canonical, __smtx_value_canonical,
    __smtx_typeof_value, __smtx_type_default, native_veq, native_and,
    Bool.and_true]
  cases __smtx_type_bounded false A <;> simp [native_ite]

/-- Lookup of an intersection of two canonical, Bool-valued set maps. -/
theorem set_inter_lookup
    (m1 m2 : SmtMap) (A : SmtType) (v : SmtValue)
    (h1Ty : __smtx_typeof_map_value m1 = SmtType.Map A SmtType.Bool)
    (h2Ty : __smtx_typeof_map_value m2 = SmtType.Map A SmtType.Bool)
    (h1Can : __smtx_map_canonical m1 = true)
    (h1Def : __smtx_map_get_default m1 = SmtValue.Boolean false) :
    __smtx_map_lookup
        (__smtx_set_op_rec true m1 m2
          (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m1))
            (SmtValue.Boolean false))) v =
      native_ite
        (native_and (native_veq (__smtx_map_lookup m1 v) (SmtValue.Boolean true))
          (native_veq (__smtx_map_lookup m2 v) (SmtValue.Boolean true)))
        (SmtValue.Boolean true) (SmtValue.Boolean false) := by
  have hAccTy :
      __smtx_typeof_map_value
          (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m1))
            (SmtValue.Boolean false)) = SmtType.Map A SmtType.Bool := by
    rw [h1Ty]
    simp [__smtx_index_typeof_map, __smtx_typeof_map_value, __smtx_typeof_value]
  rw [mss_op_lookup_acc true (m1 := m1) (m2 := m2)
    (acc := SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m1))
      (SmtValue.Boolean false))
    (A := A) (i := v) h1Ty h2Ty hAccTy h1Can (map_canonical_default _) h1Def]
  simp [__smtx_map_lookup, native_veq, native_iff, SmtEval.native_and, native_ite]

/-- Lookup of a difference of two canonical, Bool-valued set maps. -/
theorem set_minus_lookup
    (m1 m2 : SmtMap) (A : SmtType) (v : SmtValue)
    (h1Ty : __smtx_typeof_map_value m1 = SmtType.Map A SmtType.Bool)
    (h2Ty : __smtx_typeof_map_value m2 = SmtType.Map A SmtType.Bool)
    (h1Can : __smtx_map_canonical m1 = true)
    (h1Def : __smtx_map_get_default m1 = SmtValue.Boolean false) :
    __smtx_map_lookup
        (__smtx_set_op_rec false m1 m2
          (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m1))
            (SmtValue.Boolean false))) v =
      native_ite
        (native_and (native_veq (__smtx_map_lookup m1 v) (SmtValue.Boolean true))
          (native_not (native_veq (__smtx_map_lookup m2 v) (SmtValue.Boolean true))))
        (SmtValue.Boolean true) (SmtValue.Boolean false) := by
  have hAccTy :
      __smtx_typeof_map_value
          (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m1))
            (SmtValue.Boolean false)) = SmtType.Map A SmtType.Bool := by
    rw [h1Ty]
    simp [__smtx_index_typeof_map, __smtx_typeof_map_value, __smtx_typeof_value]
  rw [mss_op_lookup_acc false (m1 := m1) (m2 := m2)
    (acc := SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m1))
      (SmtValue.Boolean false))
    (A := A) (i := v) h1Ty h2Ty hAccTy h1Can (map_canonical_default _) h1Def]
  simp [__smtx_map_lookup, native_veq, native_iff, SmtEval.native_and, native_ite,
    native_not]

theorem veq_false_of_model_eval_eq_false {v1 v2 : SmtValue}
    (h : __smtx_model_eval_eq v1 v2 = SmtValue.Boolean false) :
    native_veq v1 v2 = false := by
  have hne : v1 ≠ v2 := by
    intro hSame; subst hSame
    rw [RuleProofs.smtx_model_eval_eq_refl v1] at h; cases h
  simpa [native_veq] using decide_eq_false hne

/-- A typed list (`@@cons` spine) all of whose elements are translatable. -/
def IsTLT : Term -> Prop
  | Term.Apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) x) y =>
      RuleProofs.eo_has_smt_translation x ∧ IsTLT y
  | Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) _ => True
  | _ => False

theorem isTLT_isTL : ∀ L : Term, IsTLT L -> IsTL L := by
  intro L
  induction L using IsTLT.induct with
  | case1 x y ih =>
      intro hTL
      obtain ⟨hx, hy⟩ := hTL
      have h2 : x ≠ Term.Stuck := RuleProofs.term_ne_stuck_of_has_smt_translation x hx
      have h3 : IsTL y := ih hy
      simp only [IsTL]
      exact ⟨h2, h3⟩
  | case2 a => intro _; trivial
  | case3 t hc1 hc2 => intro hTL; exact absurd hTL (by cases t <;> simp_all [IsTLT])

theorem isTLT_sutl : ∀ nf : Term,
    RuleProofs.eo_has_smt_translation nf -> __set_union_to_list nf ≠ Term.Stuck ->
    IsTLT (__set_union_to_list nf) := by
  intro nf
  induction nf using __set_union_to_list.induct with
  | case1 e t ih =>
      intro hTrans hNS
      have hsutlt : __set_union_to_list t ≠ Term.Stuck := by
        intro hSt; apply hNS
        show __eo_mk_apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) e)
            (__set_union_to_list t) = Term.Stuck
        rw [hSt]; rfl
      unfold RuleProofs.eo_has_smt_translation at hTrans
      have hSU : __eo_to_smt
          (((Term.UOp UserOp.set_union).Apply
            ((Term.UOp UserOp.set_singleton).Apply e)).Apply t)
          = SmtTerm.set_union
            (__eo_to_smt ((Term.UOp UserOp.set_singleton).Apply e)) (__eo_to_smt t) := rfl
      rw [hSU] at hTrans
      obtain ⟨A, hAse, hAt⟩ := set_binop_args_of_non_none (op := SmtTerm.set_union)
        (typeof_set_union_eq _ _) hTrans
      have hTransSe : RuleProofs.eo_has_smt_translation
          ((Term.UOp UserOp.set_singleton).Apply e) := by
        unfold RuleProofs.eo_has_smt_translation; rw [hAse]; simp
      have hTransT : RuleProofs.eo_has_smt_translation t := by
        unfold RuleProofs.eo_has_smt_translation; rw [hAt]; simp
      rw [show __set_union_to_list (((Term.UOp UserOp.set_union).Apply
            ((Term.UOp UserOp.set_singleton).Apply e)).Apply t)
          = __eo_mk_apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) e)
            (__set_union_to_list t) from rfl,
        mk_apply_of_ne_stuck (by simp) hsutlt]
      exact ⟨singleton_elem_trans hTransSe, ih hTransT hsutlt⟩
  | case2 T => intro _ _; trivial
  | case3 e =>
      intro hTrans hNS
      have hnilne :
          __eo_nil (Term.UOp UserOp._at__at_TypedList_cons) (__eo_typeof e) ≠ Term.Stuck := by
        intro hSt; apply hNS
        show __eo_mk_apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) e)
            (__eo_nil (Term.UOp UserOp._at__at_TypedList_cons) (__eo_typeof e)) = Term.Stuck
        rw [hSt]; rfl
      have hnilform :
          __eo_nil (Term.UOp UserOp._at__at_TypedList_cons) (__eo_typeof e) =
            Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) (__eo_typeof e) := by
        cases h : __eo_typeof e <;>
          simp_all [__eo_nil, __eo_nil__at__at_TypedList_cons]
      rw [show __set_union_to_list ((Term.UOp UserOp.set_singleton).Apply e)
          = __eo_mk_apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) e)
            (__eo_nil (Term.UOp UserOp._at__at_TypedList_cons) (__eo_typeof e)) from rfl,
        hnilform, mk_apply_of_ne_stuck (by simp) (by simp)]
      exact ⟨singleton_elem_trans hTrans, trivial⟩
  | case4 g hc1 hc2 hc3 =>
      intro _ hNS
      exact absurd (by unfold __set_union_to_list; split <;> simp_all) hNS

theorem find_rec_cons (f x y a : Term) (k : native_Int) (ha : a ≠ Term.Stuck) :
    __eo_list_find_rec (Term.Apply (Term.Apply f x) y) a (Term.Numeral k) =
      __eo_ite (__eo_eq x a) (Term.Numeral k)
        (__eo_list_find_rec y a (__eo_add (Term.Numeral k) (Term.Numeral 1))) := by
  cases a <;> first | (exact absurd rfl ha) | rfl

/-- A syntactic `find` hit implies model-membership. -/
theorem findMem (M : SmtModel) :
    ∀ L : Term, IsTL L -> ∀ (a : Term) (k : native_Int), a ≠ Term.Stuck ->
      __eo_is_neg (__eo_list_find_rec L a (Term.Numeral k)) = Term.Boolean false ->
      listLookup M L (__smtx_model_eval M (__eo_to_smt a)) = SmtValue.Boolean true := by
  intro L
  induction L using IsTL.induct with
  | case1 x y ih =>
      intro hTL a k ha hneg
      obtain ⟨hxne, hyTL⟩ := hTL
      rw [find_rec_cons (Term.UOp UserOp._at__at_TypedList_cons) x y a k ha,
        eo_eq_val x a hxne ha] at hneg
      cases hax : native_teq a x
      · rw [hax, eo_ite_false,
          show __eo_add (Term.Numeral k) (Term.Numeral 1)
            = Term.Numeral (native_zplus k 1) from rfl] at hneg
        have hrec := ih hyTL a (native_zplus k 1) ha hneg
        rw [listLookup_cons]
        cases native_veq (__smtx_model_eval M (__eo_to_smt x))
            (__smtx_model_eval M (__eo_to_smt a)) <;> simp [native_ite, hrec]
      · have hax' : a = x := of_decide_eq_true hax
        rw [listLookup_cons, hax']
        simp [native_ite, native_veq]
  | case2 T =>
      intro hTL a k ha hneg
      rw [show __eo_list_find_rec (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) T) a
          (Term.Numeral k) = Term.Numeral (-1 : native_Int) from by
        cases a <;> first | (exact absurd rfl ha) | rfl,
        show __eo_is_neg (Term.Numeral (-1 : native_Int)) = Term.Boolean true from by
          native_decide] at hneg
      cases hneg
  | case3 t hc1 hc2 =>
      intro hTL
      exact absurd hTL (by cases t <;> simp_all [IsTL])

/-- `findMem` lifted through the `__eo_list_find` wrapper for a typed list. -/
theorem findMem' (M : SmtModel) (L a : Term) (hTL : IsTL L) (ha : a ≠ Term.Stuck)
    (hneg : __eo_is_neg (__eo_list_find (Term.UOp UserOp._at__at_TypedList_cons) L a)
      = Term.Boolean false) :
    listLookup M L (__smtx_model_eval M (__eo_to_smt a)) = SmtValue.Boolean true := by
  rw [show __eo_list_find (Term.UOp UserOp._at__at_TypedList_cons) L a
      = __eo_list_find_rec L a (Term.Numeral 0) from by
    rw [show __eo_list_find (Term.UOp UserOp._at__at_TypedList_cons) L a
        = __eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) L)
          (Term.Boolean true) (__eo_list_find_rec L a (Term.Numeral 0)) from rfl,
      isTL_is_list L hTL, req_tt]] at hneg
  exact findMem M L hTL a 0 ha hneg

theorem eo_ite_then_eq_true {g X : Term}
    (h : __eo_ite g X (Term.Boolean false) = Term.Boolean true) :
    g = Term.Boolean true ∧ X = Term.Boolean true := by
  unfold __eo_ite at h
  cases hg : native_teq g (Term.Boolean true)
  · rw [hg] at h
    simp only [native_ite] at h
    cases hg2 : native_teq g (Term.Boolean false) <;> rw [hg2] at h <;>
      simp at h
  · rw [hg] at h
    simp only [native_ite] at h
    exact ⟨by simpa [native_teq] using hg, h⟩

theorem distinct_list_rec_cons (a s xs T : Term) (ha : a ≠ Term.Stuck)
    (hT : T ≠ Term.Stuck) :
    __are_distinct_terms_list_rec a
        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) s) xs) T =
      __eo_ite (__eo_ite (__eo_eq a s) (Term.Boolean false)
          (__are_distinct_terms_type a s T))
        (__are_distinct_terms_list_rec a xs T) (Term.Boolean false) := by
  cases a <;> cases T <;>
    first | (exact absurd rfl ha) | (exact absurd rfl hT) | rfl

/-- A successful `are_distinct_terms_list` check implies model non-membership. -/
theorem distinctNonMem (M : SmtModel) (hM : model_wf M) (a : Term)
    (ha : RuleProofs.eo_has_smt_translation a) :
    ∀ L : Term, IsTLT L ->
      __are_distinct_terms_list_rec a L (__eo_typeof a) = Term.Boolean true ->
      listLookup M L (__smtx_model_eval M (__eo_to_smt a)) = SmtValue.Boolean false := by
  have haNe : a ≠ Term.Stuck := RuleProofs.term_ne_stuck_of_has_smt_translation a ha
  intro L
  induction L using IsTLT.induct with
  | case1 s xs ih =>
      intro hTLT hDist
      obtain ⟨hsTrans, hxsTLT⟩ := hTLT
      by_cases hT : __eo_typeof a = Term.Stuck
      · rw [hT,
          show __are_distinct_terms_list_rec a
              (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) s) xs)
              Term.Stuck = Term.Stuck from by
            cases a <;> first | (exact absurd rfl haNe) | rfl] at hDist
        cases hDist
      · rw [distinct_list_rec_cons a s xs (__eo_typeof a) haNe hT] at hDist
        obtain ⟨hGuard, hListRec⟩ := eo_ite_then_eq_true hDist
        obtain ⟨hEqFalse, hDistType⟩ := eo_ite_eq_false_guard_true hGuard
        have hEvalEqFalse := are_distinct_terms_type_model_eval_eq_false M hM a s ha
          hsTrans hEqFalse hDistType
        have hveq_as := veq_false_of_model_eval_eq_false hEvalEqFalse
        have hne : __smtx_model_eval M (__eo_to_smt s) ≠
            __smtx_model_eval M (__eo_to_smt a) := by
          intro he; rw [he] at hveq_as; simp [native_veq] at hveq_as
        have hveq : native_veq (__smtx_model_eval M (__eo_to_smt s))
            (__smtx_model_eval M (__eo_to_smt a)) = false := by
          simpa [native_veq] using decide_eq_false hne
        rw [listLookup_cons, hveq]
        simpa [native_ite] using ih hxsTLT hListRec
  | case2 T => intro _ _; rfl
  | case3 t hc1 hc2 => intro hTLT; exact absurd hTLT (by cases t <;> simp_all [IsTLT])

theorem native_veq_self (v : SmtValue) : native_veq v v = true := by
  simp [native_veq]

theorem find_rec_numeral :
    ∀ L : Term, IsTL L -> ∀ (a : Term) (k : native_Int), a ≠ Term.Stuck ->
      ∃ m : native_Int, __eo_list_find_rec L a (Term.Numeral k) = Term.Numeral m := by
  intro L
  induction L using IsTL.induct with
  | case1 x y ih =>
      intro hTL a k ha
      obtain ⟨hxne, hyTL⟩ := hTL
      rw [find_rec_cons (Term.UOp UserOp._at__at_TypedList_cons) x y a k ha,
        eo_eq_val x a hxne ha]
      cases hax : native_teq a x
      · rw [eo_ite_false,
          show __eo_add (Term.Numeral k) (Term.Numeral 1)
            = Term.Numeral (native_zplus k 1) from rfl]
        exact ih hyTL a (native_zplus k 1) ha
      · rw [eo_ite_true]; exact ⟨k, rfl⟩
  | case2 T =>
      intro hTL a k ha
      exact ⟨-1, by cases a <;> first | (exact absurd rfl ha) | rfl⟩
  | case3 t hc1 hc2 => intro hTL; exact absurd hTL (by cases t <;> simp_all [IsTL])

theorem find_is_neg_bool (L a : Term) (hTL : IsTL L) (ha : a ≠ Term.Stuck) :
    ∃ b, __eo_is_neg (__eo_list_find (Term.UOp UserOp._at__at_TypedList_cons) L a) =
      Term.Boolean b := by
  rw [show __eo_list_find (Term.UOp UserOp._at__at_TypedList_cons) L a
      = __eo_list_find_rec L a (Term.Numeral 0) from by
    rw [show __eo_list_find (Term.UOp UserOp._at__at_TypedList_cons) L a
        = __eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) L)
          (Term.Boolean true) (__eo_list_find_rec L a (Term.Numeral 0)) from rfl,
      isTL_is_list L hTL, req_tt]]
  obtain ⟨m, hm⟩ := find_rec_numeral L hTL a 0 ha
  rw [hm]; exact ⟨native_zlt m 0, rfl⟩

theorem eval_inter_cons (a as L_t : Term) (hLt : L_t ≠ Term.Stuck) :
    __eval_sets_inter
        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) a) as) L_t =
      __eo_ite (__eo_is_neg (__eo_list_find (Term.UOp UserOp._at__at_TypedList_cons) L_t a))
        (__eo_requires (__are_distinct_terms_list_rec a L_t (__eo_typeof a))
          (Term.Boolean true) (__eval_sets_inter as L_t))
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) a)
          (__eval_sets_inter as L_t)) := by
  cases L_t <;> first | (exact absurd rfl hLt) | rfl

theorem eval_inter_nil (T L_t : Term) (hLt : L_t ≠ Term.Stuck) :
    __eval_sets_inter (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) T) L_t =
      Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) T := by
  cases L_t <;> first | (exact absurd rfl hLt) | rfl

/-- Membership characterisation of the intersection list evaluator. -/
theorem listLookup_eval_inter (M : SmtModel) (hM : model_wf M) :
    ∀ L_s : Term, IsTLT L_s -> ∀ L_t : Term, IsTLT L_t ->
      __eval_sets_inter L_s L_t ≠ Term.Stuck -> ∀ v : SmtValue,
      listLookup M (__eval_sets_inter L_s L_t) v =
        native_ite
          (native_and (native_veq (listLookup M L_s v) (SmtValue.Boolean true))
            (native_veq (listLookup M L_t v) (SmtValue.Boolean true)))
          (SmtValue.Boolean true) (SmtValue.Boolean false) := by
  intro L_s
  induction L_s using IsTLT.induct with
  | case1 a as ih =>
      intro hLsTLT L_t hLtTLT hNe v
      obtain ⟨haTrans, hasTLT⟩ := hLsTLT
      have haNe := RuleProofs.term_ne_stuck_of_has_smt_translation a haTrans
      have hLtTL := isTLT_isTL L_t hLtTLT
      have hLtNe := isTL_ne_stuck hLtTL
      obtain ⟨b, hb⟩ := find_is_neg_bool L_t a hLtTL haNe
      rw [eval_inter_cons a as L_t hLtNe, hb] at hNe ⊢
      cases b
      · -- found: keep
        rw [eo_ite_false] at hNe ⊢
        have hv0Ne : __eval_sets_inter as L_t ≠ Term.Stuck := by
          intro h0; apply hNe; rw [h0]; rfl
        rw [mk_apply_of_ne_stuck (by simp) hv0Ne, listLookup_cons]
        have hihv := ih hasTLT L_t hLtTLT hv0Ne v
        have hmem := findMem' M L_t a hLtTL haNe hb
        rw [listLookup_cons]
        cases hav : native_veq (__smtx_model_eval M (__eo_to_smt a)) v
        · simp only [native_ite]; exact hihv
        · have hva : v = __smtx_model_eval M (__eo_to_smt a) :=
            (eq_of_native_veq_true hav).symm
          subst hva
          rw [hmem]; simp [native_ite, native_veq_self, native_and]
      · -- not found: drop
        rw [eo_ite_true] at hNe ⊢
        have hDist := req_arg_eq hNe
        have hRes := req_result hNe
        rw [hRes] at hNe ⊢
        have hihv := ih hasTLT L_t hLtTLT hNe v
        have hnonmem := distinctNonMem M hM a haTrans L_t hLtTLT hDist
        rw [listLookup_cons]
        cases hav : native_veq (__smtx_model_eval M (__eo_to_smt a)) v
        · simp only [native_ite]; exact hihv
        · have hva : v = __smtx_model_eval M (__eo_to_smt a) :=
            (eq_of_native_veq_true hav).symm
          subst hva
          rw [hihv, hnonmem]; simp [native_ite, native_veq, native_and]
  | case2 T =>
      intro hLsTLT L_t hLtTLT hNe v
      have hLtNe := isTL_ne_stuck (isTLT_isTL L_t hLtTLT)
      rw [eval_inter_nil T L_t hLtNe]
      have hnil : listLookup M (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) T) v =
        SmtValue.Boolean false := rfl
      rw [hnil]; simp [native_ite, native_veq, native_and]
  | case3 t hc1 hc2 => intro hLsTLT; exact absurd hLsTLT (by cases t <;> simp_all [IsTLT])

theorem eval_minus_cons (a as L_t : Term) (hLt : L_t ≠ Term.Stuck) :
    __eval_sets_minus
        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) a) as) L_t =
      __eo_ite (__eo_is_neg (__eo_list_find (Term.UOp UserOp._at__at_TypedList_cons) L_t a))
        (__eo_requires (__are_distinct_terms_list_rec a L_t (__eo_typeof a))
          (Term.Boolean true)
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) a)
            (__eval_sets_minus as L_t)))
        (__eval_sets_minus as L_t) := by
  cases L_t <;> first | (exact absurd rfl hLt) | rfl

theorem eval_minus_nil (T L_t : Term) (hLt : L_t ≠ Term.Stuck) :
    __eval_sets_minus (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) T) L_t =
      Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) T := by
  cases L_t <;> first | (exact absurd rfl hLt) | rfl

/-- Membership characterisation of the difference list evaluator. -/
theorem listLookup_eval_minus (M : SmtModel) (hM : model_wf M) :
    ∀ L_s : Term, IsTLT L_s -> ∀ L_t : Term, IsTLT L_t ->
      __eval_sets_minus L_s L_t ≠ Term.Stuck -> ∀ v : SmtValue,
      listLookup M (__eval_sets_minus L_s L_t) v =
        native_ite
          (native_and (native_veq (listLookup M L_s v) (SmtValue.Boolean true))
            (native_not (native_veq (listLookup M L_t v) (SmtValue.Boolean true))))
          (SmtValue.Boolean true) (SmtValue.Boolean false) := by
  intro L_s
  induction L_s using IsTLT.induct with
  | case1 a as ih =>
      intro hLsTLT L_t hLtTLT hNe v
      obtain ⟨haTrans, hasTLT⟩ := hLsTLT
      have haNe := RuleProofs.term_ne_stuck_of_has_smt_translation a haTrans
      have hLtTL := isTLT_isTL L_t hLtTLT
      have hLtNe := isTL_ne_stuck hLtTL
      obtain ⟨b, hb⟩ := find_is_neg_bool L_t a hLtTL haNe
      rw [eval_minus_cons a as L_t hLtNe, hb] at hNe ⊢
      cases b
      · -- found: drop
        rw [eo_ite_false] at hNe ⊢
        have hihv := ih hasTLT L_t hLtTLT hNe v
        have hmem := findMem' M L_t a hLtTL haNe hb
        rw [listLookup_cons]
        cases hav : native_veq (__smtx_model_eval M (__eo_to_smt a)) v
        · simp only [native_ite]; exact hihv
        · have hva : v = __smtx_model_eval M (__eo_to_smt a) :=
            (eq_of_native_veq_true hav).symm
          subst hva
          rw [hihv, hmem]; simp [native_ite, native_veq, native_and, native_not]
      · -- not found: keep
        rw [eo_ite_true] at hNe ⊢
        have hDist := req_arg_eq hNe
        have hRes := req_result hNe
        rw [hRes] at hNe ⊢
        have hv0Ne : __eval_sets_minus as L_t ≠ Term.Stuck := by
          intro h0; apply hNe; rw [h0]; rfl
        rw [mk_apply_of_ne_stuck (by simp) hv0Ne, listLookup_cons]
        have hihv := ih hasTLT L_t hLtTLT hv0Ne v
        have hnonmem := distinctNonMem M hM a haTrans L_t hLtTLT hDist
        rw [listLookup_cons]
        cases hav : native_veq (__smtx_model_eval M (__eo_to_smt a)) v
        · simp only [native_ite]; exact hihv
        · have hva : v = __smtx_model_eval M (__eo_to_smt a) :=
            (eq_of_native_veq_true hav).symm
          subst hva
          rw [hnonmem]; simp [native_ite, native_veq, native_and, native_not]
  | case2 T =>
      intro hLsTLT L_t hLtTLT hNe v
      have hLtNe := isTL_ne_stuck (isTLT_isTL L_t hLtTLT)
      rw [eval_minus_nil T L_t hLtNe]
      have hnil : listLookup M (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) T) v =
        SmtValue.Boolean false := rfl
      rw [hnil]; simp [native_ite, native_veq, native_and]
  | case3 t hc1 hc2 => intro hLsTLT; exact absurd hLsTLT (by cases t <;> simp_all [IsTLT])

theorem eval_inter_isTL : ∀ L_s : Term, IsTLT L_s -> ∀ L_t : Term, IsTLT L_t ->
    __eval_sets_inter L_s L_t ≠ Term.Stuck -> IsTL (__eval_sets_inter L_s L_t) := by
  intro L_s
  induction L_s using IsTLT.induct with
  | case1 a as ih =>
      intro hLsTLT L_t hLtTLT hNe
      obtain ⟨haTrans, hasTLT⟩ := hLsTLT
      have haNe := RuleProofs.term_ne_stuck_of_has_smt_translation a haTrans
      have hLtNe := isTL_ne_stuck (isTLT_isTL L_t hLtTLT)
      obtain ⟨bb, hb⟩ := find_is_neg_bool L_t a (isTLT_isTL L_t hLtTLT) haNe
      rw [eval_inter_cons a as L_t hLtNe, hb] at hNe ⊢
      cases bb
      · rw [eo_ite_false] at hNe ⊢
        have hv0Ne : __eval_sets_inter as L_t ≠ Term.Stuck := by
          intro h0; apply hNe; rw [h0]; rfl
        rw [mk_apply_of_ne_stuck (by simp) hv0Ne]
        simp only [IsTL]; exact ⟨haNe, ih hasTLT L_t hLtTLT hv0Ne⟩
      · rw [eo_ite_true] at hNe ⊢
        have hRes := req_result hNe
        rw [hRes] at hNe ⊢
        exact ih hasTLT L_t hLtTLT hNe
  | case2 T =>
      intro _ L_t hLtTLT hNe
      rw [eval_inter_nil T L_t (isTL_ne_stuck (isTLT_isTL L_t hLtTLT))]; trivial
  | case3 t hc1 hc2 => intro hLsTLT; exact absurd hLsTLT (by cases t <;> simp_all [IsTLT])

theorem eval_minus_isTL : ∀ L_s : Term, IsTLT L_s -> ∀ L_t : Term, IsTLT L_t ->
    __eval_sets_minus L_s L_t ≠ Term.Stuck -> IsTL (__eval_sets_minus L_s L_t) := by
  intro L_s
  induction L_s using IsTLT.induct with
  | case1 a as ih =>
      intro hLsTLT L_t hLtTLT hNe
      obtain ⟨haTrans, hasTLT⟩ := hLsTLT
      have haNe := RuleProofs.term_ne_stuck_of_has_smt_translation a haTrans
      have hLtNe := isTL_ne_stuck (isTLT_isTL L_t hLtTLT)
      obtain ⟨bb, hb⟩ := find_is_neg_bool L_t a (isTLT_isTL L_t hLtTLT) haNe
      rw [eval_minus_cons a as L_t hLtNe, hb] at hNe ⊢
      cases bb
      · rw [eo_ite_false] at hNe ⊢
        exact ih hasTLT L_t hLtTLT hNe
      · rw [eo_ite_true] at hNe ⊢
        have hRes := req_result hNe
        rw [hRes] at hNe ⊢
        have hv0Ne : __eval_sets_minus as L_t ≠ Term.Stuck := by
          intro h0; apply hNe; rw [h0]; rfl
        rw [mk_apply_of_ne_stuck (by simp) hv0Ne]
        simp only [IsTL]; exact ⟨haNe, ih hasTLT L_t hLtTLT hv0Ne⟩
  | case2 T =>
      intro _ L_t hLtTLT hNe
      rw [eval_minus_nil T L_t (isTL_ne_stuck (isTLT_isTL L_t hLtTLT))]; trivial
  | case3 t hc1 hc2 => intro hLsTLT; exact absurd hLsTLT (by cases t <;> simp_all [IsTLT])

/-- The `__eo_list_meq` guard being `true` forces `__eval_sets_op a` to be non-stuck,
hence `a` is a set union/intersection/difference. -/
theorem guard_eval_ne_stuck (a b : Term)
    (hGuard : __eo_list_meq (Term.UOp UserOp._at__at_TypedList_cons)
        (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons) (__eval_sets_op a))
        (__set_union_to_list b) = Term.Boolean true) :
    __eval_sets_op a ≠ Term.Stuck := by
  rw [show __eo_list_meq (Term.UOp UserOp._at__at_TypedList_cons)
        (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons) (__eval_sets_op a))
        (__set_union_to_list b) =
      __eo_and
        (__eo_list_minclude_rec
          (__eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons)
            (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons) (__eval_sets_op a)))
            (Term.Boolean true)
            (__eo_get_elements_rec (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons)
              (__eval_sets_op a))))
          (__eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons)
            (__set_union_to_list b)) (Term.Boolean true)
            (__eo_get_elements_rec (__set_union_to_list b)))
          (Term.Boolean true))
        (__eo_list_minclude_rec
          (__eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons)
            (__set_union_to_list b)) (Term.Boolean true)
            (__eo_get_elements_rec (__set_union_to_list b)))
          (__eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons)
            (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons) (__eval_sets_op a)))
            (Term.Boolean true)
            (__eo_get_elements_rec (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons)
              (__eval_sets_op a))))
          (Term.Boolean true)) from rfl] at hGuard
  obtain ⟨hXY, _⟩ := eo_and_eq_true hGuard
  have hreqXne :
      __eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons)
        (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons) (__eval_sets_op a)))
        (Term.Boolean true)
        (__eo_get_elements_rec (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons)
          (__eval_sets_op a))) ≠ Term.Stuck := by
    intro h0; rw [h0] at hXY; simp [__eo_list_minclude_rec] at hXY
  have hSetofNe := is_list_cons_ne_stuck (req_arg_eq hreqXne)
  obtain ⟨hListEval, _⟩ := setof_parts hSetofNe
  exact is_list_cons_ne_stuck hListEval

/-- For the `set.union` case, the proven equality is sound: the operands have equal
SMT set-model values. -/
theorem union_model_eval_rel
    (M : SmtModel) (hM : model_wf M) (s t b : Term)
    (hTransU : RuleProofs.eo_has_smt_translation
      ((Term.Apply (Term.Apply (Term.UOp UserOp.set_union) s) t)))
    (hTransB : RuleProofs.eo_has_smt_translation b)
    (hSameTy : __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_union) s) t)) =
      __smtx_typeof (__eo_to_smt b))
    (hGuard : __eo_list_meq (Term.UOp UserOp._at__at_TypedList_cons)
        (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons)
          (__eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_union) s) t)))
        (__set_union_to_list b) = Term.Boolean true) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_union) s) t)))
      (__smtx_model_eval M (__eo_to_smt b)) := by
  -- Types of the operands.
  have hTransU' := hTransU
  unfold RuleProofs.eo_has_smt_translation at hTransU'
  have hSU : __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_union) s) t)
      = SmtTerm.set_union (__eo_to_smt s) (__eo_to_smt t) := rfl
  rw [hSU] at hTransU'
  obtain ⟨A, hAs, hAt⟩ := set_binop_args_of_non_none (op := SmtTerm.set_union)
    (typeof_set_union_eq _ _) hTransU'
  have hUTyA : __smtx_typeof
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_union) s) t)) =
      SmtType.Set A := by
    rw [hSU, typeof_set_union_eq, hAs, hAt]
    simp [__smtx_typeof_sets_op_2, native_ite, native_Teq]
  have hBTyA : __smtx_typeof (__eo_to_smt b) = SmtType.Set A := by rw [← hSameTy, hUTyA]
  have hTransS : RuleProofs.eo_has_smt_translation s := by
    unfold RuleProofs.eo_has_smt_translation; rw [hAs]; simp
  have hTransT : RuleProofs.eo_has_smt_translation t := by
    unfold RuleProofs.eo_has_smt_translation; rw [hAt]; simp
  obtain ⟨ms, hmseval, hmscan, hmsty, hmsdef⟩ := set_value_facts M hM s A hTransS hAs
  obtain ⟨mt, hmteval, hmtcan, hmtty, hmtdef⟩ := set_value_facts M hM t A hTransT hAt
  obtain ⟨mu, hmueval, hmucan, hmuty, hmudef⟩ := set_value_facts M hM _ A hTransU hUTyA
  obtain ⟨mb, hmbeval, hmbcan, hmbty, hmbdef⟩ := set_value_facts M hM b A hTransB hBTyA
  -- Extract from the guard that the two `meq` requirement wrappers are non-stuck.
  have hEvalEq : __eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_union) s) t)
      = __eo_list_concat (Term.UOp UserOp._at__at_TypedList_cons)
        (__set_union_to_list s) (__set_union_to_list t) := rfl
  rw [show __eo_list_meq (Term.UOp UserOp._at__at_TypedList_cons)
        (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons)
          (__eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_union) s) t)))
        (__set_union_to_list b) =
      __eo_and
        (__eo_list_minclude_rec
          (__eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons)
            (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons)
              (__eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_union) s) t))))
            (Term.Boolean true)
            (__eo_get_elements_rec (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons)
              (__eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_union) s) t)))))
          (__eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons)
            (__set_union_to_list b)) (Term.Boolean true)
            (__eo_get_elements_rec (__set_union_to_list b)))
          (Term.Boolean true))
        (__eo_list_minclude_rec
          (__eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons)
            (__set_union_to_list b)) (Term.Boolean true)
            (__eo_get_elements_rec (__set_union_to_list b)))
          (__eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons)
            (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons)
              (__eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_union) s) t))))
            (Term.Boolean true)
            (__eo_get_elements_rec (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons)
              (__eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_union) s) t)))))
          (Term.Boolean true)) from rfl] at hGuard
  obtain ⟨hXY, hYX⟩ := eo_and_eq_true hGuard
  have hreqXne :
      __eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons)
        (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons)
          (__eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_union) s) t))))
        (Term.Boolean true)
        (__eo_get_elements_rec (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons)
          (__eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_union) s) t))))
        ≠ Term.Stuck := by
    intro h0; rw [h0] at hXY; simp [__eo_list_minclude_rec] at hXY
  have hreqYne :
      __eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons)
        (__set_union_to_list b)) (Term.Boolean true)
        (__eo_get_elements_rec (__set_union_to_list b)) ≠ Term.Stuck := by
    intro h0; rw [h0] at hYX; simp [__eo_list_minclude_rec] at hYX
  -- Hence the `is_list` checks hold, peeling the wrappers.
  have hListB : __eo_is_list (Term.UOp UserOp._at__at_TypedList_cons)
      (__set_union_to_list b) = Term.Boolean true := req_arg_eq hreqYne
  have hsutlb : __set_union_to_list b ≠ Term.Stuck := is_list_cons_ne_stuck hListB
  have hListX : __eo_is_list (Term.UOp UserOp._at__at_TypedList_cons)
      (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons)
        (__eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_union) s) t)))
      = Term.Boolean true := req_arg_eq hreqXne
  have hSetofNe : __eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons)
      (__eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_union) s) t))
      ≠ Term.Stuck := is_list_cons_ne_stuck hListX
  obtain ⟨hListEval, hSetofEq⟩ := setof_parts hSetofNe
  have hEvalNe : __eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_union) s) t)
      ≠ Term.Stuck := is_list_cons_ne_stuck hListEval
  rw [hEvalEq] at hEvalNe
  obtain ⟨hListS, hListT, hConcatEq⟩ := concat_parts hEvalNe
  have hsutls : __set_union_to_list s ≠ Term.Stuck := is_list_cons_ne_stuck hListS
  have hsutlt : __set_union_to_list t ≠ Term.Stuck := is_list_cons_ne_stuck hListT
  -- Typed-list well-formedness.
  have hTLs := isTL_sutl s hTransS hsutls
  have hTLt := isTL_sutl t hTransT hsutlt
  have hTLb := isTL_sutl b hTransB hsutlb
  have hELs := isTL_isElemList _ hTLs
  have hELt := isTL_isElemList _ hTLt
  have hELb := isTL_isElemList _ hTLb
  have hELeval : IsElemList
      (__eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_union) s) t)) := by
    rw [hEvalEq, hConcatEq]
    exact concat_rec_isElemList _ _ hELs hELt
  have hELsetof : IsElemList (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons)
      (__eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_union) s) t))) := by
    rw [hSetofEq]; exact setof_rec_isElemList _ hELeval
  -- The union map equals the merge of the operand maps.
  have hMU : __smtx_set_union (SmtValue.Set ms) (SmtValue.Set mt) = SmtValue.Set mu := by
    rw [← hmseval, ← hmteval, ← model_eval_union_eq]; exact hmueval
  rw [__smtx_set_union] at hMU
  injection hMU with hmuEq
  -- Pointwise lookup equality.
  have hLookEq : ∀ v, __smtx_map_lookup mu v = __smtx_map_lookup mb v := by
    intro v
    have hLU : __smtx_map_lookup mu v =
        native_ite (native_veq (__smtx_map_lookup ms v) (SmtValue.Boolean true))
          (SmtValue.Boolean true) (__smtx_map_lookup mt v) := by
      rw [← hmuEq, set_union_lookup ms mt A v hmsty hmtty hmscan hmtcan hmsdef]
    have hLs := set_nf_lookup M hM s ms v hsutls hTransS hmseval
    have hLt := set_nf_lookup M hM t mt v hsutlt hTransT hmteval
    have hLb := set_nf_lookup M hM b mb v hsutlb hTransB hmbeval
    have hMeqV := listLookup_meq M _ _ v hELsetof hELb hGuard
    rw [hSetofEq] at hMeqV
    rw [listLookup_setof M v _ hELeval] at hMeqV
    rw [hEvalEq, hConcatEq, listLookup_concat M v _ _ hELs hsutlt] at hMeqV
    rw [hLU, hLs, hLt, hLb, ← hMeqV]
  -- Conclude via set extensionality.
  rw [hmueval, hmbeval]
  exact RuleProofs.smt_value_rel_set_of_lookup_eq mu mb hmucan hmbcan
    (by rw [set_default_leaf hmucan hmuty hmudef,
      set_default_leaf hmbcan hmbty hmbdef]) hLookEq

/-- For the `set.inter` case, the proven equality is sound. -/
theorem inter_model_eval_rel
    (M : SmtModel) (hM : model_wf M) (s t b : Term)
    (hTransU : RuleProofs.eo_has_smt_translation
      ((Term.Apply (Term.Apply (Term.UOp UserOp.set_inter) s) t)))
    (hTransB : RuleProofs.eo_has_smt_translation b)
    (hSameTy : __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_inter) s) t)) =
      __smtx_typeof (__eo_to_smt b))
    (hGuard : __eo_list_meq (Term.UOp UserOp._at__at_TypedList_cons)
        (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons)
          (__eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_inter) s) t)))
        (__set_union_to_list b) = Term.Boolean true) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_inter) s) t)))
      (__smtx_model_eval M (__eo_to_smt b)) := by
  have hTransU' := hTransU
  unfold RuleProofs.eo_has_smt_translation at hTransU'
  have hSU : __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_inter) s) t)
      = SmtTerm.set_inter (__eo_to_smt s) (__eo_to_smt t) := rfl
  rw [hSU] at hTransU'
  obtain ⟨A, hAs, hAt⟩ := set_binop_args_of_non_none (op := SmtTerm.set_inter)
    (typeof_set_inter_eq _ _) hTransU'
  have hUTyA : __smtx_typeof
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_inter) s) t)) =
      SmtType.Set A := by
    rw [hSU, typeof_set_inter_eq, hAs, hAt]
    simp [__smtx_typeof_sets_op_2, native_ite, native_Teq]
  have hBTyA : __smtx_typeof (__eo_to_smt b) = SmtType.Set A := by rw [← hSameTy, hUTyA]
  have hTransS : RuleProofs.eo_has_smt_translation s := by
    unfold RuleProofs.eo_has_smt_translation; rw [hAs]; simp
  have hTransT : RuleProofs.eo_has_smt_translation t := by
    unfold RuleProofs.eo_has_smt_translation; rw [hAt]; simp
  obtain ⟨ms, hmseval, hmscan, hmsty, hmsdef⟩ := set_value_facts M hM s A hTransS hAs
  obtain ⟨mt, hmteval, hmtcan, hmtty, hmtdef⟩ := set_value_facts M hM t A hTransT hAt
  obtain ⟨mu, hmueval, hmucan, hmuty, hmudef⟩ := set_value_facts M hM _ A hTransU hUTyA
  obtain ⟨mb, hmbeval, hmbcan, hmbty, hmbdef⟩ := set_value_facts M hM b A hTransB hBTyA
  have hEvalEq : __eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_inter) s) t)
      = __eval_sets_inter (__set_union_to_list s) (__set_union_to_list t) := rfl
  have hEvalNeOp := guard_eval_ne_stuck _ b hGuard
  rw [show __eo_list_meq (Term.UOp UserOp._at__at_TypedList_cons)
        (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons)
          (__eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_inter) s) t)))
        (__set_union_to_list b) =
      __eo_and
        (__eo_list_minclude_rec
          (__eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons)
            (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons)
              (__eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_inter) s) t))))
            (Term.Boolean true)
            (__eo_get_elements_rec (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons)
              (__eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_inter) s) t)))))
          (__eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons)
            (__set_union_to_list b)) (Term.Boolean true)
            (__eo_get_elements_rec (__set_union_to_list b)))
          (Term.Boolean true))
        (__eo_list_minclude_rec
          (__eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons)
            (__set_union_to_list b)) (Term.Boolean true)
            (__eo_get_elements_rec (__set_union_to_list b)))
          (__eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons)
            (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons)
              (__eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_inter) s) t))))
            (Term.Boolean true)
            (__eo_get_elements_rec (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons)
              (__eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_inter) s) t)))))
          (Term.Boolean true)) from rfl] at hGuard
  obtain ⟨hXY, hYX⟩ := eo_and_eq_true hGuard
  have hreqYne :
      __eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons)
        (__set_union_to_list b)) (Term.Boolean true)
        (__eo_get_elements_rec (__set_union_to_list b)) ≠ Term.Stuck := by
    intro h0; rw [h0] at hYX; simp [__eo_list_minclude_rec] at hYX
  have hListB : __eo_is_list (Term.UOp UserOp._at__at_TypedList_cons)
      (__set_union_to_list b) = Term.Boolean true := req_arg_eq hreqYne
  have hsutlb : __set_union_to_list b ≠ Term.Stuck := is_list_cons_ne_stuck hListB
  -- The two operand lists are non-stuck typed lists.
  have hsutlt : __set_union_to_list t ≠ Term.Stuck := by
    intro h0; apply hEvalNeOp; rw [hEvalEq, h0]
    cases __set_union_to_list s <;> rfl
  have hsutls : __set_union_to_list s ≠ Term.Stuck := by
    intro h0; apply hEvalNeOp; rw [hEvalEq, h0]
    cases __set_union_to_list t <;> rfl
  have hEvalNe : __eval_sets_inter (__set_union_to_list s) (__set_union_to_list t)
      ≠ Term.Stuck := by rw [← hEvalEq]; exact hEvalNeOp
  have hTLTs := isTLT_sutl s hTransS hsutls
  have hTLTt := isTLT_sutl t hTransT hsutlt
  have hTLTb := isTLT_sutl b hTransB hsutlb
  have hELb := isTL_isElemList _ (isTLT_isTL _ hTLTb)
  have hELeval : IsElemList
      (__eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_inter) s) t)) := by
    rw [hEvalEq]; exact isTL_isElemList _ (eval_inter_isTL _ hTLTs _ hTLTt hEvalNe)
  have hreqXne :
      __eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons)
        (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons)
          (__eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_inter) s) t))))
        (Term.Boolean true)
        (__eo_get_elements_rec (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons)
          (__eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_inter) s) t))))
        ≠ Term.Stuck := by
    intro h0; rw [h0] at hXY; simp [__eo_list_minclude_rec] at hXY
  obtain ⟨_, hSetofEq⟩ := setof_parts (is_list_cons_ne_stuck (req_arg_eq hreqXne))
  have hELsetof : IsElemList (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons)
      (__eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_inter) s) t))) := by
    rw [hSetofEq]; exact setof_rec_isElemList _ hELeval
  have hMU : __smtx_set_inter (SmtValue.Set ms) (SmtValue.Set mt) = SmtValue.Set mu := by
    rw [← hmseval, ← hmteval, ← model_eval_inter_eq]; exact hmueval
  rw [__smtx_set_inter] at hMU
  injection hMU with hmuEq
  have hLookEq : ∀ v, __smtx_map_lookup mu v = __smtx_map_lookup mb v := by
    intro v
    have hLU : __smtx_map_lookup mu v =
        native_ite (native_and
          (native_veq (__smtx_map_lookup ms v) (SmtValue.Boolean true))
          (native_veq (__smtx_map_lookup mt v) (SmtValue.Boolean true)))
          (SmtValue.Boolean true) (SmtValue.Boolean false) := by
      rw [← hmuEq, set_inter_lookup ms mt A v hmsty hmtty hmscan hmsdef]
    have hLs := set_nf_lookup M hM s ms v hsutls hTransS hmseval
    have hLt := set_nf_lookup M hM t mt v hsutlt hTransT hmteval
    have hLb := set_nf_lookup M hM b mb v hsutlb hTransB hmbeval
    have hMeqV := listLookup_meq M _ _ v hELsetof hELb hGuard
    rw [hSetofEq, listLookup_setof M v _ hELeval, hEvalEq,
      listLookup_eval_inter M hM _ hTLTs _ hTLTt hEvalNe v] at hMeqV
    rw [hLU, hLs, hLt, hMeqV, ← hLb]
  rw [hmueval, hmbeval]
  exact RuleProofs.smt_value_rel_set_of_lookup_eq mu mb hmucan hmbcan
    (by rw [set_default_leaf hmucan hmuty hmudef,
      set_default_leaf hmbcan hmbty hmbdef]) hLookEq

/-- For the `set.minus` case, the proven equality is sound. -/
theorem minus_model_eval_rel
    (M : SmtModel) (hM : model_wf M) (s t b : Term)
    (hTransU : RuleProofs.eo_has_smt_translation
      ((Term.Apply (Term.Apply (Term.UOp UserOp.set_minus) s) t)))
    (hTransB : RuleProofs.eo_has_smt_translation b)
    (hSameTy : __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_minus) s) t)) =
      __smtx_typeof (__eo_to_smt b))
    (hGuard : __eo_list_meq (Term.UOp UserOp._at__at_TypedList_cons)
        (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons)
          (__eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_minus) s) t)))
        (__set_union_to_list b) = Term.Boolean true) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_minus) s) t)))
      (__smtx_model_eval M (__eo_to_smt b)) := by
  have hTransU' := hTransU
  unfold RuleProofs.eo_has_smt_translation at hTransU'
  have hSU : __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_minus) s) t)
      = SmtTerm.set_minus (__eo_to_smt s) (__eo_to_smt t) := rfl
  rw [hSU] at hTransU'
  obtain ⟨A, hAs, hAt⟩ := set_binop_args_of_non_none (op := SmtTerm.set_minus)
    (typeof_set_minus_eq _ _) hTransU'
  have hUTyA : __smtx_typeof
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_minus) s) t)) =
      SmtType.Set A := by
    rw [hSU, typeof_set_minus_eq, hAs, hAt]
    simp [__smtx_typeof_sets_op_2, native_ite, native_Teq]
  have hBTyA : __smtx_typeof (__eo_to_smt b) = SmtType.Set A := by rw [← hSameTy, hUTyA]
  have hTransS : RuleProofs.eo_has_smt_translation s := by
    unfold RuleProofs.eo_has_smt_translation; rw [hAs]; simp
  have hTransT : RuleProofs.eo_has_smt_translation t := by
    unfold RuleProofs.eo_has_smt_translation; rw [hAt]; simp
  obtain ⟨ms, hmseval, hmscan, hmsty, hmsdef⟩ := set_value_facts M hM s A hTransS hAs
  obtain ⟨mt, hmteval, hmtcan, hmtty, hmtdef⟩ := set_value_facts M hM t A hTransT hAt
  obtain ⟨mu, hmueval, hmucan, hmuty, hmudef⟩ := set_value_facts M hM _ A hTransU hUTyA
  obtain ⟨mb, hmbeval, hmbcan, hmbty, hmbdef⟩ := set_value_facts M hM b A hTransB hBTyA
  have hEvalEq : __eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_minus) s) t)
      = __eval_sets_minus (__set_union_to_list s) (__set_union_to_list t) := rfl
  have hEvalNeOp := guard_eval_ne_stuck _ b hGuard
  rw [show __eo_list_meq (Term.UOp UserOp._at__at_TypedList_cons)
        (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons)
          (__eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_minus) s) t)))
        (__set_union_to_list b) =
      __eo_and
        (__eo_list_minclude_rec
          (__eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons)
            (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons)
              (__eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_minus) s) t))))
            (Term.Boolean true)
            (__eo_get_elements_rec (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons)
              (__eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_minus) s) t)))))
          (__eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons)
            (__set_union_to_list b)) (Term.Boolean true)
            (__eo_get_elements_rec (__set_union_to_list b)))
          (Term.Boolean true))
        (__eo_list_minclude_rec
          (__eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons)
            (__set_union_to_list b)) (Term.Boolean true)
            (__eo_get_elements_rec (__set_union_to_list b)))
          (__eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons)
            (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons)
              (__eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_minus) s) t))))
            (Term.Boolean true)
            (__eo_get_elements_rec (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons)
              (__eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_minus) s) t)))))
          (Term.Boolean true)) from rfl] at hGuard
  obtain ⟨hXY, hYX⟩ := eo_and_eq_true hGuard
  have hreqYne :
      __eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons)
        (__set_union_to_list b)) (Term.Boolean true)
        (__eo_get_elements_rec (__set_union_to_list b)) ≠ Term.Stuck := by
    intro h0; rw [h0] at hYX; simp [__eo_list_minclude_rec] at hYX
  have hListB : __eo_is_list (Term.UOp UserOp._at__at_TypedList_cons)
      (__set_union_to_list b) = Term.Boolean true := req_arg_eq hreqYne
  have hsutlb : __set_union_to_list b ≠ Term.Stuck := is_list_cons_ne_stuck hListB
  -- The two operand lists are non-stuck typed lists.
  have hsutlt : __set_union_to_list t ≠ Term.Stuck := by
    intro h0; apply hEvalNeOp; rw [hEvalEq, h0]
    cases __set_union_to_list s <;> rfl
  have hsutls : __set_union_to_list s ≠ Term.Stuck := by
    intro h0; apply hEvalNeOp; rw [hEvalEq, h0]
    cases __set_union_to_list t <;> rfl
  have hEvalNe : __eval_sets_minus (__set_union_to_list s) (__set_union_to_list t)
      ≠ Term.Stuck := by rw [← hEvalEq]; exact hEvalNeOp
  have hTLTs := isTLT_sutl s hTransS hsutls
  have hTLTt := isTLT_sutl t hTransT hsutlt
  have hTLTb := isTLT_sutl b hTransB hsutlb
  have hELb := isTL_isElemList _ (isTLT_isTL _ hTLTb)
  have hELeval : IsElemList
      (__eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_minus) s) t)) := by
    rw [hEvalEq]; exact isTL_isElemList _ (eval_minus_isTL _ hTLTs _ hTLTt hEvalNe)
  have hreqXne :
      __eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons)
        (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons)
          (__eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_minus) s) t))))
        (Term.Boolean true)
        (__eo_get_elements_rec (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons)
          (__eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_minus) s) t))))
        ≠ Term.Stuck := by
    intro h0; rw [h0] at hXY; simp [__eo_list_minclude_rec] at hXY
  obtain ⟨_, hSetofEq⟩ := setof_parts (is_list_cons_ne_stuck (req_arg_eq hreqXne))
  have hELsetof : IsElemList (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons)
      (__eval_sets_op (Term.Apply (Term.Apply (Term.UOp UserOp.set_minus) s) t))) := by
    rw [hSetofEq]; exact setof_rec_isElemList _ hELeval
  have hMU : __smtx_set_minus (SmtValue.Set ms) (SmtValue.Set mt) = SmtValue.Set mu := by
    rw [← hmseval, ← hmteval, ← model_eval_minus_eq]; exact hmueval
  rw [__smtx_set_minus] at hMU
  injection hMU with hmuEq
  have hLookEq : ∀ v, __smtx_map_lookup mu v = __smtx_map_lookup mb v := by
    intro v
    have hLU : __smtx_map_lookup mu v =
        native_ite (native_and
          (native_veq (__smtx_map_lookup ms v) (SmtValue.Boolean true))
          (native_not (native_veq (__smtx_map_lookup mt v) (SmtValue.Boolean true))))
          (SmtValue.Boolean true) (SmtValue.Boolean false) := by
      rw [← hmuEq, set_minus_lookup ms mt A v hmsty hmtty hmscan hmsdef]
    have hLs := set_nf_lookup M hM s ms v hsutls hTransS hmseval
    have hLt := set_nf_lookup M hM t mt v hsutlt hTransT hmteval
    have hLb := set_nf_lookup M hM b mb v hsutlb hTransB hmbeval
    have hMeqV := listLookup_meq M _ _ v hELsetof hELb hGuard
    rw [hSetofEq, listLookup_setof M v _ hELeval, hEvalEq,
      listLookup_eval_minus M hM _ hTLTs _ hTLTt hEvalNe v] at hMeqV
    rw [hLU, hLs, hLt, hMeqV, ← hLb]
  rw [hmueval, hmbeval]
  exact RuleProofs.smt_value_rel_set_of_lookup_eq mu mb hmucan hmbcan
    (by rw [set_default_leaf hmucan hmuty hmudef,
      set_default_leaf hmbcan hmbty hmbdef]) hLookEq

end SetsEvalOpSupport
