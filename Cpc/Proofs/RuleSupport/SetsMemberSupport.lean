module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.Canonical
import all Cpc.Proofs.Canonical

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace SetsMemberSupport

theorem eo_typeof_or_ne_stuck
    {A B : Term}
    (h : __eo_typeof_or A B ≠ Term.Stuck) :
    A = Term.Bool ∧ B = Term.Bool := by
  cases A <;> cases B <;> simp [__eo_typeof_or] at h ⊢

theorem eo_typeof_eq_eq_bool_info
    {A B : Term}
    (h : __eo_typeof_eq A B = Term.Bool) :
    A = B ∧ A ≠ Term.Stuck := by
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_eq] at h
  by_cases hB : B = Term.Stuck
  · subst B
    cases A <;> simp [__eo_typeof_eq] at h
  have hReq :
      __eo_requires (__eo_eq A B) (Term.Boolean true) Term.Bool =
        Term.Bool := by
    simpa [__eo_typeof_eq, hA, hB] using h
  have hReqNS :
      __eo_requires (__eo_eq A B) (Term.Boolean true) Term.Bool ≠
        Term.Stuck := by
    rw [hReq]
    decide
  have hBA : B = A :=
    RuleProofs.eq_of_requires_eq_true_not_stuck A B Term.Bool hReqNS
  exact ⟨hBA.symm, hA⟩

theorem eo_typeof_set_member_eq_bool_info
    {A B : Term}
    (h : __eo_typeof_set_member A B = Term.Bool) :
    ∃ T : Term,
      A = T ∧
        B = Term.Apply (Term.UOp UserOp.Set) T ∧
          T ≠ Term.Stuck := by
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_set_member] at h
  cases B <;> try simp [__eo_typeof_set_member] at h
  next f U =>
    cases f <;> try simp at h
    next op =>
      cases op <;> try simp at h
      have hReq :
          __eo_requires (__eo_eq A U) (Term.Boolean true) Term.Bool =
            Term.Bool := by
        simpa [__eo_typeof_set_member, hA] using h
      have hReqNS :
          __eo_requires (__eo_eq A U) (Term.Boolean true) Term.Bool ≠
            Term.Stuck := by
        rw [hReq]
        decide
      have hUA : U = A :=
        RuleProofs.eq_of_requires_eq_true_not_stuck A U Term.Bool hReqNS
      subst U
      exact ⟨A, rfl, rfl, hA⟩

theorem map_cons_head_key_type
    {k v : SmtValue} {m : SmtMap} {A B : SmtType}
    (hTy : __smtx_typeof_map_value (SmtMap.cons k v m) = SmtType.Map A B) :
    __smtx_typeof_value k = A := by
  by_cases hEq :
      native_Teq (SmtType.Map (__smtx_typeof_value k) (__smtx_typeof_value v))
        (__smtx_typeof_map_value m)
  · have hTail : __smtx_typeof_map_value m = SmtType.Map A B := by
      simpa [__smtx_typeof_map_value, native_ite, hEq] using hTy
    have hHead :
        SmtType.Map (__smtx_typeof_value k) (__smtx_typeof_value v) =
          SmtType.Map A B := by
      have hEq' :
          SmtType.Map (__smtx_typeof_value k) (__smtx_typeof_value v) =
            __smtx_typeof_map_value m := by
        simpa [native_Teq] using hEq
      exact hEq'.trans hTail
    cases hHead
    rfl
  · simp [__smtx_typeof_map_value, native_ite, hEq] at hTy

theorem map_cons_head_value_type
    {k v : SmtValue} {m : SmtMap} {A B : SmtType}
    (hTy : __smtx_typeof_map_value (SmtMap.cons k v m) = SmtType.Map A B) :
    __smtx_typeof_value v = B := by
  by_cases hEq :
      native_Teq (SmtType.Map (__smtx_typeof_value k) (__smtx_typeof_value v))
        (__smtx_typeof_map_value m)
  · have hTail : __smtx_typeof_map_value m = SmtType.Map A B := by
      simpa [__smtx_typeof_map_value, native_ite, hEq] using hTy
    have hHead :
        SmtType.Map (__smtx_typeof_value k) (__smtx_typeof_value v) =
          SmtType.Map A B := by
      have hEq' :
          SmtType.Map (__smtx_typeof_value k) (__smtx_typeof_value v) =
            __smtx_typeof_map_value m := by
        simpa [native_Teq] using hEq
      exact hEq'.trans hTail
    cases hHead
    rfl
  · simp [__smtx_typeof_map_value, native_ite, hEq] at hTy

theorem map_cons_tail_type
    {k v : SmtValue} {m : SmtMap} {A B : SmtType}
    (hTy : __smtx_typeof_map_value (SmtMap.cons k v m) = SmtType.Map A B) :
    __smtx_typeof_map_value m = SmtType.Map A B := by
  by_cases hEq :
      native_Teq (SmtType.Map (__smtx_typeof_value k) (__smtx_typeof_value v))
        (__smtx_typeof_map_value m)
  · simpa [__smtx_typeof_map_value, native_ite, hEq] using hTy
  · simp [__smtx_typeof_map_value, native_ite, hEq] at hTy

theorem map_cons_tail_canonical
    {k v : SmtValue} {m : SmtMap}
    (hCan : __smtx_map_canonical (SmtMap.cons k v m) = true) :
    __smtx_map_canonical m = true := by
  have hParts := hCan
  simp [__smtx_map_canonical, SmtEval.native_and] at hParts
  exact hParts.1.1.2

theorem map_cons_head_key_canonical
    {k v : SmtValue} {m : SmtMap}
    (hCan : __smtx_map_canonical (SmtMap.cons k v m) = true) :
    value_canonical k := by
  have hParts := hCan
  simp [__smtx_map_canonical, SmtEval.native_and] at hParts
  exact hParts.1.1.1.1

theorem map_cons_tail_ordered
    {k v : SmtValue} {m : SmtMap}
    (hCan : __smtx_map_canonical (SmtMap.cons k v m) = true) :
    __smtx_map_entries_ordered_after k m = true := by
  have hParts := hCan
  simp [__smtx_map_canonical, SmtEval.native_and] at hParts
  exact hParts.1.2

theorem set_map_cons_entry_true
    {k v : SmtValue} {m : SmtMap} {A : SmtType}
    (hTy : __smtx_typeof_map_value (SmtMap.cons k v m) =
      SmtType.Map A SmtType.Bool)
    (hCan : __smtx_map_canonical (SmtMap.cons k v m) = true)
    (hDef : __smtx_map_get_default (SmtMap.cons k v m) = SmtValue.Boolean false) :
    v = SmtValue.Boolean true := by
  have hvTy : __smtx_typeof_value v = SmtType.Bool :=
    map_cons_head_value_type hTy
  rcases bool_value_canonical hvTy with ⟨b, rfl⟩
  cases b
  · have hNeDefault : native_veq (SmtValue.Boolean false)
        (__smtx_map_get_default m) = false := by
      have hParts := hCan
      simp [__smtx_map_canonical, SmtEval.native_and, SmtEval.native_not] at hParts
      exact hParts.2
    have hTailDef : __smtx_map_get_default m = SmtValue.Boolean false := by
      simpa [__smtx_map_get_default] using hDef
    simp [hTailDef, native_veq] at hNeDefault
  · rfl

theorem mss_op_lookup_acc
    (isInter : native_Bool) :
    ∀ {m1 m2 acc : SmtMap} {A : SmtType} {i : SmtValue},
      __smtx_typeof_map_value m1 = SmtType.Map A SmtType.Bool ->
      __smtx_typeof_map_value m2 = SmtType.Map A SmtType.Bool ->
      __smtx_typeof_map_value acc = SmtType.Map A SmtType.Bool ->
      __smtx_map_canonical m1 = true ->
      __smtx_map_canonical acc = true ->
      __smtx_map_get_default m1 = SmtValue.Boolean false ->
      __smtx_map_lookup (__smtx_set_op_rec isInter m1 m2 acc) i =
        native_ite
          (native_and
            (native_veq (__smtx_map_lookup m1 i) (SmtValue.Boolean true))
            (native_iff
              (native_veq (__smtx_map_lookup m2 i) (SmtValue.Boolean true))
              isInter))
          (SmtValue.Boolean true)
          (__smtx_map_lookup acc i)
  | SmtMap.default T efalse, m2, acc, A, i, hm1Ty, hm2Ty, haccTy, hm1Can,
      haccCan, hm1Def => by
      have hefalse : efalse = SmtValue.Boolean false := by
        simpa [__smtx_map_get_default] using hm1Def
      simp [__smtx_set_op_rec, __smtx_map_lookup, hefalse, native_veq,
        SmtEval.native_and, native_ite, native_iff]
  | SmtMap.cons e etrue m1, m2, acc, A, i, hm1Ty, hm2Ty, haccTy, hm1Can,
      haccCan, hm1Def => by
      have hmTailTy : __smtx_typeof_map_value m1 = SmtType.Map A SmtType.Bool :=
        map_cons_tail_type hm1Ty
      have heTy : __smtx_typeof_value e = A :=
        map_cons_head_key_type hm1Ty
      have hmTailCan : __smtx_map_canonical m1 = true :=
        map_cons_tail_canonical hm1Can
      have heCan : value_canonical e :=
        map_cons_head_key_canonical hm1Can
      have hOrdTail : __smtx_map_entries_ordered_after e m1 = true :=
        map_cons_tail_ordered hm1Can
      have hmTailDef : __smtx_map_get_default m1 = SmtValue.Boolean false := by
        simpa [__smtx_map_get_default] using hm1Def
      have hetrue : etrue = SmtValue.Boolean true :=
        set_map_cons_entry_true hm1Ty hm1Can hm1Def
      subst etrue
      by_cases hCond :
          native_veq (__smtx_map_lookup m2 e) (SmtValue.Boolean true) = isInter
      · let acc' :=
          __smtx_map_update_aux (__smtx_map_get_default acc) acc e
            (SmtValue.Boolean true)
        have hCondDec :
            decide (__smtx_map_lookup m2 e = SmtValue.Boolean true) = isInter := by
          simpa [native_veq] using hCond
        have hacc'Ty : __smtx_typeof_map_value acc' = SmtType.Map A SmtType.Bool := by
          dsimp [acc']
          exact map_canon_insert_typed haccTy heTy rfl
        have hacc'Can : __smtx_map_canonical acc' = true := by
          dsimp [acc']
          exact map_update_aux_canonical haccCan heCan (value_canonical_boolean true)
        have hRec := mss_op_lookup_acc isInter (m1 := m1) (m2 := m2) (acc := acc')
          (A := A) (i := i) hmTailTy hm2Ty hacc'Ty hmTailCan hacc'Can
          hmTailDef
        cases hei : native_veq e i
        · have hAccLookup :
              __smtx_map_lookup acc' i = __smtx_map_lookup acc i := by
            dsimp [acc']
            exact map_lookup_update_aux_other haccCan hei
          simpa [__smtx_set_op_rec, hCond, hCondDec, __smtx_map_lookup,
            native_ite, native_iff, hei, hAccLookup] using hRec
        · have heiEq : e = i := eq_of_native_veq_true hei
          subst i
          have hTailLookup :
              __smtx_map_lookup m1 e = SmtValue.Boolean false := by
            calc
              __smtx_map_lookup m1 e = __smtx_map_get_default m1 :=
                map_lookup_eq_default_of_entries_ordered_after hmTailCan hOrdTail
              _ = SmtValue.Boolean false := hmTailDef
          have hAccLookup :
              __smtx_map_lookup acc' e = SmtValue.Boolean true := by
            dsimp [acc']
            exact map_lookup_update_aux_same haccCan
          simpa [__smtx_set_op_rec, hCond, hCondDec, __smtx_map_lookup,
            native_ite, native_iff, native_veq, hTailLookup, hAccLookup,
            SmtEval.native_and] using hRec
      · have hRec := mss_op_lookup_acc isInter (m1 := m1) (m2 := m2) (acc := acc)
          (A := A) (i := i) hmTailTy hm2Ty haccTy hmTailCan haccCan hmTailDef
        have hCondDec :
            ¬ decide (__smtx_map_lookup m2 e = SmtValue.Boolean true) = isInter := by
          intro h
          exact hCond (by simpa [native_veq] using h)
        cases hei : native_veq e i
        · -- the two sides differ only in a stale `Decidable` instance, which
          -- `simpa`'s closing step no longer accepts but `exact` still does.
          simp only [__smtx_set_op_rec, hCond, __smtx_map_lookup,
            native_ite, native_iff, hei] at hRec ⊢
          exact hRec
        · have heiEq : e = i := eq_of_native_veq_true hei
          subst i
          have hTailLookup :
              __smtx_map_lookup m1 e = SmtValue.Boolean false := by
            calc
              __smtx_map_lookup m1 e = __smtx_map_get_default m1 :=
                map_lookup_eq_default_of_entries_ordered_after hmTailCan hOrdTail
              _ = SmtValue.Boolean false := hmTailDef
          simpa [__smtx_set_op_rec, hCond, hCondDec, __smtx_map_lookup,
            native_ite, native_iff, native_veq, hTailLookup,
            SmtEval.native_and] using hRec

/-- Every lookup into a bool-valued map of type `Map A Bool` yields a Bool
    value, regardless of the index type. -/
theorem set_map_lookup_bool :
    ∀ {m : SmtMap} {A : SmtType} {i : SmtValue},
      __smtx_typeof_map_value m = SmtType.Map A SmtType.Bool ->
        __smtx_typeof_value (__smtx_map_lookup m i) = SmtType.Bool
  | SmtMap.default T e, A, i, hTy => by
      have heTy : __smtx_typeof_value e = SmtType.Bool := by
        have h : SmtType.Map T (__smtx_typeof_value e) =
            SmtType.Map A SmtType.Bool := by
          simpa [__smtx_typeof_map_value] using hTy
        exact (SmtType.Map.injEq _ _ _ _ ▸ h).2
      simpa [__smtx_map_lookup] using heTy
  | SmtMap.cons k v m, A, i, hTy => by
      have hmTy : __smtx_typeof_map_value m = SmtType.Map A SmtType.Bool :=
        map_cons_tail_type hTy
      have hvTy : __smtx_typeof_value v = SmtType.Bool :=
        map_cons_head_value_type hTy
      cases hki : native_veq k i
      · simpa [__smtx_map_lookup, native_ite, hki] using
          set_map_lookup_bool (m := m) (A := A) (i := i) hmTy
      · simpa [__smtx_map_lookup, native_ite, hki] using hvTy

/-- The default leaf of a canonical bool-valued map of type `Map A Bool`
    is `SmtMap.default A (Boolean false)`. -/
theorem set_map_default_leaf_eq :
    ∀ {m : SmtMap} {A : SmtType},
      __smtx_typeof_map_value m = SmtType.Map A SmtType.Bool ->
        __smtx_map_get_default m = SmtValue.Boolean false ->
          smt_map_default_leaf m = SmtMap.default A (SmtValue.Boolean false)
  | SmtMap.default T e, A, hTy, hDef => by
      have hTA : T = A := by
        have h : SmtType.Map T (__smtx_typeof_value e) =
            SmtType.Map A SmtType.Bool := by
          simpa [__smtx_typeof_map_value] using hTy
        exact (SmtType.Map.injEq _ _ _ _ ▸ h).1
      subst hTA
      have heDef : e = SmtValue.Boolean false := by
        simpa [__smtx_map_get_default] using hDef
      simp [smt_map_default_leaf, heDef]
  | SmtMap.cons k v m, A, hTy, hDef => by
      have hmTy : __smtx_typeof_map_value m = SmtType.Map A SmtType.Bool :=
        map_cons_tail_type hTy
      have hmDef : __smtx_map_get_default m = SmtValue.Boolean false := by
        simpa [__smtx_map_get_default] using hDef
      simpa [smt_map_default_leaf] using set_map_default_leaf_eq hmTy hmDef

/--
Pointwise lookup of the intersection of two canonical bool maps:
`(inter mx my)[i] = true` iff `mx[i] = true ∧ my[i] = true`.
-/
theorem set_inter_lookup
    {mx my : SmtMap} {A : SmtType} {i : SmtValue}
    (hMxTy : __smtx_typeof_map_value mx = SmtType.Map A SmtType.Bool)
    (hMyTy : __smtx_typeof_map_value my = SmtType.Map A SmtType.Bool)
    (hMxCan : __smtx_map_canonical mx = true)
    (hMxDef : __smtx_map_get_default mx = SmtValue.Boolean false) :
    __smtx_map_lookup
        (__smtx_set_op_rec true mx my
          (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value mx))
            (SmtValue.Boolean false)))
        i =
      native_ite
        (native_and
          (native_veq (__smtx_map_lookup mx i) (SmtValue.Boolean true))
          (native_veq (__smtx_map_lookup my i) (SmtValue.Boolean true)))
        (SmtValue.Boolean true)
        (SmtValue.Boolean false) := by
  have hIdx : __smtx_index_typeof_map (__smtx_typeof_map_value mx) = A := by
    rw [hMxTy]; rfl
  rw [hIdx]
  have hEmptyTy :
      __smtx_typeof_map_value (SmtMap.default A (SmtValue.Boolean false)) =
        SmtType.Map A SmtType.Bool := by
    simp [__smtx_typeof_map_value, __smtx_typeof_value]
  have hEmptyCan :
      __smtx_map_canonical (SmtMap.default A (SmtValue.Boolean false)) = true :=
    Smtm.set_empty_map_canonical A
  have hAcc := mss_op_lookup_acc true (m1 := mx) (m2 := my)
    (acc := SmtMap.default A (SmtValue.Boolean false)) (A := A) (i := i)
    hMxTy hMyTy hEmptyTy hMxCan hEmptyCan hMxDef
  rw [hAcc]
  simp [__smtx_map_lookup, native_iff, native_ite, SmtEval.native_and]

/--
Pointwise lookup of the union of two canonical bool maps:
`(union mx my)[i] = true` iff `mx[i] = true ∨ my[i] = true`.
-/
theorem set_union_lookup
    {mx my : SmtMap} {A : SmtType} {i : SmtValue}
    (hMxTy : __smtx_typeof_map_value mx = SmtType.Map A SmtType.Bool)
    (hMyTy : __smtx_typeof_map_value my = SmtType.Map A SmtType.Bool)
    (hMxCan : __smtx_map_canonical mx = true)
    (hMyCan : __smtx_map_canonical my = true)
    (hMxDef : __smtx_map_get_default mx = SmtValue.Boolean false)
    (hMyLookupTy : __smtx_typeof_value (__smtx_map_lookup my i) = SmtType.Bool) :
    __smtx_map_lookup
        (__smtx_set_op_rec false mx
          (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value mx))
            (SmtValue.Boolean false))
          my)
        i =
      native_ite
        (native_veq (__smtx_map_lookup mx i) (SmtValue.Boolean true))
        (SmtValue.Boolean true)
        (__smtx_map_lookup my i) := by
  have hIdx : __smtx_index_typeof_map (__smtx_typeof_map_value mx) = A := by
    rw [hMxTy]; rfl
  rw [hIdx]
  have hEmptyTy :
      __smtx_typeof_map_value (SmtMap.default A (SmtValue.Boolean false)) =
        SmtType.Map A SmtType.Bool := by
    simp [__smtx_typeof_map_value, __smtx_typeof_value]
  have hAcc := mss_op_lookup_acc false (m1 := mx)
    (m2 := SmtMap.default A (SmtValue.Boolean false)) (acc := my) (A := A) (i := i)
    hMxTy hEmptyTy hMyTy hMxCan hMyCan hMxDef
  rw [hAcc]
  -- (default A false)[i] = false, so (false ↔ false) = true
  simp [__smtx_map_lookup, native_iff, native_ite, SmtEval.native_and, native_veq]

/--
The core set-theoretic equivalence underlying `sets_subset_elim`:
for canonical bool-valued maps `mx`, `my` over the same index type `A`,
`(inter mx my) = mx` as sets iff `(union mx my) = my` as sets.

Both are equivalent to `mx ⊆ my` (pointwise `mx[i] = true → my[i] = true`),
so the two `native_veq` Booleans coincide.
-/
theorem set_subset_inter_eq_union_veq
    {mx my : SmtMap} {A : SmtType}
    (hMxTy : __smtx_typeof_map_value mx = SmtType.Map A SmtType.Bool)
    (hMyTy : __smtx_typeof_map_value my = SmtType.Map A SmtType.Bool)
    (hMxCan : __smtx_map_canonical mx = true)
    (hMyCan : __smtx_map_canonical my = true)
    (hMxDef : __smtx_map_get_default mx = SmtValue.Boolean false)
    (hMyDef : __smtx_map_get_default my = SmtValue.Boolean false) :
    native_veq (__smtx_set_inter (SmtValue.Set mx) (SmtValue.Set my))
        (SmtValue.Set mx) =
      native_veq (__smtx_set_union (SmtValue.Set mx) (SmtValue.Set my))
        (SmtValue.Set my) := by
  -- name the two operation maps
  let interMap : SmtMap := __smtx_set_op_rec true mx my (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value mx)) (SmtValue.Boolean false))
  let unionMap : SmtMap := __smtx_set_op_rec false mx (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value mx)) (SmtValue.Boolean false)) my
  have hInterDef : interMap = __smtx_set_op_rec true mx my (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value mx)) (SmtValue.Boolean false)) := rfl
  have hUnionDef : unionMap = __smtx_set_op_rec false mx (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value mx)) (SmtValue.Boolean false)) my := rfl
  have hInterEq :
      __smtx_set_inter (SmtValue.Set mx) (SmtValue.Set my) = SmtValue.Set interMap := by
    rw [hInterDef]; simp [__smtx_set_inter]
  have hUnionEq :
      __smtx_set_union (SmtValue.Set mx) (SmtValue.Set my) = SmtValue.Set unionMap := by
    rw [hUnionDef]; simp [__smtx_set_union]
  rw [hInterEq, hUnionEq]
  -- empty index = A
  have hIdx : __smtx_index_typeof_map (__smtx_typeof_map_value mx) = A := by
    rw [hMxTy]; rfl
  have hEmptyTy :
      __smtx_typeof_map_value (SmtMap.default A (SmtValue.Boolean false)) =
        SmtType.Map A SmtType.Bool := by
    simp [__smtx_typeof_map_value, __smtx_typeof_value]
  -- type / canonicity / default-leaf of interMap
  have hInterTy : __smtx_typeof_map_value interMap = SmtType.Map A SmtType.Bool := by
    rw [hInterDef, hIdx]
    exact Smtm.mss_op_internal_typed true hMxTy hMyTy hEmptyTy
  have hInterCan : __smtx_map_canonical interMap = true := by
    rw [hInterDef]
    exact Smtm.mss_op_internal_canonical true hMxCan (by
      rw [hIdx]; exact Smtm.set_empty_map_canonical A)
  have hInterGetDef :
      __smtx_map_get_default interMap = SmtValue.Boolean false := by
    rw [hInterDef]
    rw [Smtm.mss_op_internal_get_default true]
    rw [hIdx]; rfl
  -- type / canonicity / default-leaf of unionMap
  have hUnionTy : __smtx_typeof_map_value unionMap = SmtType.Map A SmtType.Bool := by
    rw [hUnionDef, hIdx]
    exact Smtm.mss_op_internal_typed false hMxTy hEmptyTy hMyTy
  have hUnionCan : __smtx_map_canonical unionMap = true := by
    rw [hUnionDef]
    exact Smtm.mss_op_internal_canonical false hMxCan hMyCan
  have hUnionGetDef :
      __smtx_map_get_default unionMap = SmtValue.Boolean false := by
    rw [hUnionDef]
    rw [Smtm.mss_op_internal_get_default false]
    exact hMyDef
  -- default leaves all equal SmtMap.default A (Boolean false)
  have hInterLeaf :
      smt_map_default_leaf interMap = SmtMap.default A (SmtValue.Boolean false) :=
    set_map_default_leaf_eq hInterTy hInterGetDef
  have hMxLeaf :
      smt_map_default_leaf mx = SmtMap.default A (SmtValue.Boolean false) :=
    set_map_default_leaf_eq hMxTy hMxDef
  have hUnionLeaf :
      smt_map_default_leaf unionMap = SmtMap.default A (SmtValue.Boolean false) :=
    set_map_default_leaf_eq hUnionTy hUnionGetDef
  have hMyLeaf :
      smt_map_default_leaf my = SmtMap.default A (SmtValue.Boolean false) :=
    set_map_default_leaf_eq hMyTy hMyDef
  -- pointwise lookup characterizations
  have hInterLookup :
      ∀ i, __smtx_map_lookup interMap i =
        native_ite
          (native_and
            (native_veq (__smtx_map_lookup mx i) (SmtValue.Boolean true))
            (native_veq (__smtx_map_lookup my i) (SmtValue.Boolean true)))
          (SmtValue.Boolean true)
          (SmtValue.Boolean false) := by
    intro i
    rw [hInterDef]
    exact set_inter_lookup hMxTy hMyTy hMxCan hMxDef
  have hUnionLookup :
      ∀ i, __smtx_typeof_value (__smtx_map_lookup my i) = SmtType.Bool ->
        __smtx_map_lookup unionMap i =
          native_ite
            (native_veq (__smtx_map_lookup mx i) (SmtValue.Boolean true))
            (SmtValue.Boolean true)
            (__smtx_map_lookup my i) := by
    intro i hMyLookupTy
    rw [hUnionDef]
    exact set_union_lookup hMxTy hMyTy hMxCan hMyCan hMxDef hMyLookupTy
  -- lookups of mx, my at any point are Bool values
  have hMxLookupTy : ∀ i, __smtx_typeof_value (__smtx_map_lookup mx i) = SmtType.Bool :=
    fun i => set_map_lookup_bool hMxTy
  have hMyLookupTy : ∀ i, __smtx_typeof_value (__smtx_map_lookup my i) = SmtType.Bool :=
    fun i => set_map_lookup_bool hMyTy
  -- reduce native_veq on Sets to structural map equality
  rw [show
      native_veq (SmtValue.Set interMap) (SmtValue.Set mx) =
        decide (interMap = mx) by
        simp [native_veq, SmtValue.Set.injEq]]
  rw [show
      native_veq (SmtValue.Set unionMap) (SmtValue.Set my) =
        decide (unionMap = my) by
        simp [native_veq, SmtValue.Set.injEq]]
  -- The "subset" predicate, pointwise
  -- Forward direction helper: interMap = mx -> mx ⊆ my pointwise
  have key :
      (interMap = mx) ↔ (unionMap = my) := by
    constructor
    · intro hIM
      -- from interMap = mx we get mx[i] = true → my[i] = true
      have hSub : ∀ i, __smtx_map_lookup mx i = SmtValue.Boolean true ->
          __smtx_map_lookup my i = SmtValue.Boolean true := by
        intro i hMxi
        have hLook := congrArg (fun m => __smtx_map_lookup m i) hIM
        rw [hInterLookup i] at hLook
        rw [hMxi] at hLook
        -- hLook : ite (and true (my[i]=true)) true false = true
        rcases bool_value_canonical (hMyLookupTy i) with ⟨b, hb⟩
        rw [hb] at hLook ⊢
        cases b
        · simp [native_ite, SmtEval.native_and, native_veq] at hLook
        · rfl
      -- now show unionMap = my by extensionality
      apply map_ext_of_lookup_eq hUnionCan hMyCan
        (by rw [hUnionLeaf, hMyLeaf])
      intro i
      rw [hUnionLookup i (hMyLookupTy i)]
      rcases bool_value_canonical (hMxLookupTy i) with ⟨bx, hbx⟩
      cases bx
      · rw [hbx]; simp [native_ite, native_veq]
      · have hMyi := hSub i (by rw [hbx])
        rw [hbx, hMyi]; simp [native_ite, native_veq]
    · intro hUM
      -- from unionMap = my we get mx[i] = true → my[i] = true
      have hSub : ∀ i, __smtx_map_lookup mx i = SmtValue.Boolean true ->
          __smtx_map_lookup my i = SmtValue.Boolean true := by
        intro i hMxi
        have hLook := congrArg (fun m => __smtx_map_lookup m i) hUM
        rw [hUnionLookup i (hMyLookupTy i)] at hLook
        rw [hMxi] at hLook
        -- hLook : ite (veq true true) true my[i] = my[i], i.e. true = my[i]
        simpa [native_ite, native_veq] using hLook.symm
      -- now show interMap = mx by extensionality
      apply map_ext_of_lookup_eq hInterCan hMxCan
        (by rw [hInterLeaf, hMxLeaf])
      intro i
      rw [hInterLookup i]
      rcases bool_value_canonical (hMxLookupTy i) with ⟨bx, hbx⟩
      cases bx
      · rw [hbx]; simp [native_ite, SmtEval.native_and, native_veq]
      · have hMyi := hSub i (by rw [hbx])
        rw [hbx, hMyi]; simp [native_ite, SmtEval.native_and, native_veq]
  rw [decide_eq_decide.mpr key]

end SetsMemberSupport
