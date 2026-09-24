module

public import Cpc.Proofs.Canonical.Order
import all Cpc.Proofs.Canonical.Order

public section

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

/-- The default leaf of a finite-map spine, retaining the type tag. -/
def smt_map_default_leaf : SmtMap -> SmtMap
  | SmtMap.cons _ _ m => smt_map_default_leaf m
  | SmtMap.default T e => SmtMap.default T e

/-- The default leaf has the same default value as the full map. -/
theorem map_default_leaf_get_default :
    ∀ (m : SmtMap),
      __smtx_map_get_default (smt_map_default_leaf m) =
        __smtx_map_get_default m
  | SmtMap.default T e => by
      simp [smt_map_default_leaf, __smtx_map_get_default]
  | SmtMap.cons i e m => by
      simpa [smt_map_default_leaf, __smtx_map_get_default] using
        map_default_leaf_get_default m

/-- The default payload of a canonical map is canonical. -/
theorem map_default_value_canonical :
    ∀ {m : SmtMap},
      __smtx_map_canonical m = true ->
        value_canonical (__smtx_map_get_default m)
  | SmtMap.default T e, h => by
      have hParts := h
      simp [__smtx_map_canonical, SmtEval.native_and] at hParts
      exact hParts.2
  | SmtMap.cons i e m, h => by
      have hm : __smtx_map_canonical m = true := by
        have hParts := h
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        rcases hParts with ⟨hMain, _hNeDefault⟩
        rcases hMain with ⟨hEntries, _hOrdered⟩
        exact hEntries.2
      simpa [__smtx_map_get_default] using map_default_value_canonical hm

/-- Entries in a canonical map have canonical values. -/
theorem map_lookup_value_canonical :
    ∀ {m : SmtMap} {i : SmtValue},
      __smtx_map_canonical m = true ->
        value_canonical (__smtx_map_lookup m i)
  | SmtMap.default T e, i, h => by
      simpa [__smtx_map_lookup, __smtx_map_get_default] using
        map_default_value_canonical (m := SmtMap.default T e) h
  | SmtMap.cons k v m, i, h => by
      have hv : value_canonical v := by
        have hParts := h
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        rcases hParts with ⟨hMain, _hNeDefault⟩
        rcases hMain with ⟨hEntries, _hOrdered⟩
        exact hEntries.1.2
      have hm : __smtx_map_canonical m = true := by
        have hParts := h
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        rcases hParts with ⟨hMain, _hNeDefault⟩
        rcases hMain with ⟨hEntries, _hOrdered⟩
        exact hEntries.2
      cases hki : native_veq k i
      · simpa [__smtx_map_lookup, native_ite, hki] using
          map_lookup_value_canonical (m := m) (i := i) hm
      · simpa [__smtx_map_lookup, native_ite, hki] using hv

/-- Canonical maps give canonical `Map` values. -/
theorem value_canonical_map_of_map_canonical
    {m : SmtMap}
    (h : __smtx_map_canonical m = true) :
    value_canonical (SmtValue.Map m) := by
  simpa [value_canonical, __smtx_value_canonical] using h

/-- Canonical maps give canonical `Set` values. -/
theorem value_canonical_set_of_map_canonical
    {m : SmtMap}
    (h : __smtx_map_canonical m = true)
    (hDef : __smtx_map_get_default m = SmtValue.Boolean false) :
    value_canonical (SmtValue.Set m) := by
  have hDefVeq :
      native_veq (__smtx_map_get_default m) (SmtValue.Boolean false) = true := by
    rw [hDef]
    simp [native_veq]
  simp [value_canonical, __smtx_value_canonical, h, hDefVeq,
    SmtEval.native_and]

/--
The non-recursive insertion helper preserves map canonicality when it is used at
a position that is already known to be ordered with respect to the tail map.
-/
theorem map_update_aux_no_default_canonical
    {m : SmtMap}
    {i e : SmtValue}
    (hm : __smtx_map_canonical m = true)
    (hi : value_canonical i)
    (he : value_canonical e)
    (hOrd : __smtx_map_entries_ordered_after i m = true) :
    __smtx_map_canonical
      (__smtx_map_update_aux_no_default (__smtx_map_get_default m) m i e) = true := by
  by_cases hEq : native_veq (__smtx_map_get_default m) e = true
  · simpa [__smtx_map_update_aux_no_default, native_ite, hEq] using hm
  · have hEqFalse : native_veq (__smtx_map_get_default m) e = false := by
      cases hEqBool : native_veq (__smtx_map_get_default m) e <;>
        simp [hEqBool] at hEq ⊢
    have hSymm : native_veq e (__smtx_map_get_default m) = false :=
      native_veq_false_symm hEqFalse
    have hiBool : __smtx_value_canonical i = true := by
      simpa [value_canonical] using hi
    have heBool : __smtx_value_canonical e = true := by
      simpa [value_canonical] using he
    simp [__smtx_map_update_aux_no_default, __smtx_map_canonical, native_ite,
      hEqFalse, hiBool, heBool, hm, hOrd, hSymm, SmtEval.native_and,
      SmtEval.native_not]

/-- The non-recursive update helper preserves the map default. -/
theorem map_update_aux_no_default_get_default
    (ed : SmtValue) (m : SmtMap) (i e : SmtValue) :
    __smtx_map_get_default (__smtx_map_update_aux_no_default ed m i e) =
      __smtx_map_get_default m := by
  cases hEq : native_veq ed e <;>
    simp [__smtx_map_update_aux_no_default, native_ite, hEq, __smtx_map_get_default]

/-- The recursive update helper preserves the map default. -/
theorem map_update_aux_get_default
    (ed : SmtValue) :
    ∀ (m : SmtMap) (i e : SmtValue),
      __smtx_map_get_default (__smtx_map_update_aux ed m i e) =
        __smtx_map_get_default m
  | SmtMap.default T d, i, e => by
      simpa [__smtx_map_update_aux] using
        map_update_aux_no_default_get_default ed (SmtMap.default T d) i e
  | SmtMap.cons k v m, i, e => by
      cases hEq : native_veq k i
      · cases hCmp : native_vcmp k i
        · simp [__smtx_map_update_aux, native_ite, hEq, hCmp,
            __smtx_map_get_default, map_update_aux_get_default ed m i e]
        · simpa [__smtx_map_update_aux, native_ite, hEq, hCmp] using
            map_update_aux_no_default_get_default ed (SmtMap.cons k v m) i e
      · simpa [__smtx_map_update_aux, native_ite, hEq,
          __smtx_map_get_default] using
          map_update_aux_no_default_get_default ed m i e

/-- The non-recursive update helper preserves the default leaf. -/
theorem map_update_aux_no_default_default_leaf
    (ed : SmtValue) (m : SmtMap) (i e : SmtValue) :
    smt_map_default_leaf (__smtx_map_update_aux_no_default ed m i e) =
      smt_map_default_leaf m := by
  cases hEq : native_veq ed e <;>
    simp [__smtx_map_update_aux_no_default, smt_map_default_leaf, native_ite, hEq]

/-- The recursive update helper preserves the default leaf. -/
theorem map_update_aux_default_leaf
    (ed : SmtValue) :
    ∀ (m : SmtMap) (i e : SmtValue),
      smt_map_default_leaf (__smtx_map_update_aux ed m i e) =
        smt_map_default_leaf m
  | SmtMap.default T d, i, e => by
      simpa [__smtx_map_update_aux] using
        map_update_aux_no_default_default_leaf ed (SmtMap.default T d) i e
  | SmtMap.cons k v m, i, e => by
      cases hEq : native_veq k i
      · cases hCmp : native_vcmp k i
        · simp [__smtx_map_update_aux, smt_map_default_leaf, native_ite, hEq,
            hCmp, map_update_aux_default_leaf ed m i e]
        · simpa [__smtx_map_update_aux, native_ite, hEq, hCmp] using
            map_update_aux_no_default_default_leaf ed (SmtMap.cons k v m) i e
      · simpa [__smtx_map_update_aux, native_ite, hEq, smt_map_default_leaf] using
          map_update_aux_no_default_default_leaf ed m i e

/--
If every entry of `m` is below `lo`, and `lo < hi`, then every entry of `m`
is below `hi`.
-/
theorem map_entries_ordered_after_trans
    (hTrans :
      ∀ {a b c : SmtValue},
        native_vcmp a b = true ->
          native_vcmp b c = true ->
            native_vcmp a c = true) :
    ∀ {m : SmtMap} {lo hi : SmtValue},
      __smtx_map_canonical m = true ->
        __smtx_map_entries_ordered_after lo m = true ->
          native_vcmp lo hi = true ->
            __smtx_map_entries_ordered_after hi m = true
  | SmtMap.default T e, lo, hi, _hm, _hOrd, _hLoHi => by
      simp [__smtx_map_entries_ordered_after]
  | SmtMap.cons k v m, lo, hi, _hm, hOrd, hLoHi => by
      exact hTrans hOrd hLoHi

/--
The one-step insertion helper preserves an external upper bound, provided the
new key is also below that bound.
-/
theorem map_update_aux_no_default_entries_ordered_after
    (hFlip :
      ∀ {a b : SmtValue},
        native_veq a b = false ->
          native_vcmp a b = false ->
            native_vcmp b a = true)
    {ed : SmtValue}
    {m : SmtMap}
    {upper i e : SmtValue}
    (hOrd : __smtx_map_entries_ordered_after upper m = true)
    (hNe : native_veq upper i = false)
    (hCmp : native_vcmp upper i = false) :
    __smtx_map_entries_ordered_after upper
      (__smtx_map_update_aux_no_default ed m i e) = true := by
  cases hEd : native_veq ed e
  · have hIUpper : native_vcmp i upper = true := hFlip hNe hCmp
    simp [__smtx_map_update_aux_no_default, native_ite, hEd,
      __smtx_map_entries_ordered_after, hIUpper]
  · simpa [__smtx_map_update_aux_no_default, native_ite, hEd] using hOrd

/--
Updating a canonical map at an index below `upper` keeps the updated map below
`upper`, assuming the intended strict-order laws of `native_vcmp`.
-/
theorem map_update_aux_entries_ordered_after
    (hFlip :
      ∀ {a b : SmtValue},
        native_veq a b = false ->
          native_vcmp a b = false ->
            native_vcmp b a = true)
    (hTrans :
      ∀ {a b c : SmtValue},
        native_vcmp a b = true ->
          native_vcmp b c = true ->
            native_vcmp a c = true) :
    ∀ (ed : SmtValue) {m : SmtMap} {upper i e : SmtValue},
      __smtx_map_canonical m = true ->
        __smtx_map_entries_ordered_after upper m = true ->
          native_veq upper i = false ->
            native_vcmp upper i = false ->
              __smtx_map_entries_ordered_after upper
                (__smtx_map_update_aux ed m i e) = true
  | ed, SmtMap.default T d, upper, i, e, _hm, _hOrd, hNe, hCmp => by
      simpa [__smtx_map_update_aux] using
        map_update_aux_no_default_entries_ordered_after hFlip
          (ed := ed) (m := SmtMap.default T d) (upper := upper)
          (i := i) (e := e) (by simp [__smtx_map_entries_ordered_after])
          hNe hCmp
  | ed, SmtMap.cons k v m, upper, i, e, hmCons, hOrdUpper, hNe, hCmp => by
      cases hEq : native_veq k i
      · cases hLt : native_vcmp k i
        · simpa [__smtx_map_update_aux, native_ite, hEq, hLt,
            __smtx_map_entries_ordered_after] using hOrdUpper
        · simpa [__smtx_map_update_aux, native_ite, hEq, hLt] using
            map_update_aux_no_default_entries_ordered_after hFlip
              (ed := ed) (m := SmtMap.cons k v m) (upper := upper)
              (i := i) (e := e) hOrdUpper hNe hCmp
      · have hki : k = i := eq_of_native_veq_true hEq
        subst i
        have hIUpper : native_vcmp k upper = true := hFlip hNe hCmp
        have hm : __smtx_map_canonical m = true := by
          have hParts := hmCons
          simp [__smtx_map_canonical, SmtEval.native_and] at hParts
          rcases hParts with ⟨hMain, _hNeDefault⟩
          rcases hMain with ⟨hEntries, _hOrdered⟩
          exact hEntries.2
        have hOrdTailK : __smtx_map_entries_ordered_after k m = true := by
          have hParts := hmCons
          simp [__smtx_map_canonical, SmtEval.native_and] at hParts
          rcases hParts with ⟨hMain, _hNeDefault⟩
          exact hMain.2
        have hOrdTailUpper : __smtx_map_entries_ordered_after upper m = true :=
          map_entries_ordered_after_trans hTrans hm hOrdTailK hIUpper
        simpa [__smtx_map_update_aux, native_ite, hEq] using
          map_update_aux_no_default_entries_ordered_after hFlip
            (ed := ed) (m := m) (upper := upper) (i := k) (e := e)
            hOrdTailUpper hNe hCmp

/--
Canonicality of the recursive map update, parameterized by the strict-order laws
that `native_vcmp` is intended to satisfy.
-/
theorem map_update_aux_canonical_of_order_laws
    (hFlip :
      ∀ {a b : SmtValue},
        native_veq a b = false ->
          native_vcmp a b = false ->
            native_vcmp b a = true)
    (hTrans :
      ∀ {a b c : SmtValue},
        native_vcmp a b = true ->
          native_vcmp b c = true ->
            native_vcmp a c = true) :
    ∀ {m : SmtMap} {i e : SmtValue},
      __smtx_map_canonical m = true ->
        value_canonical i ->
          value_canonical e ->
            __smtx_map_canonical
              (__smtx_map_update_aux (__smtx_map_get_default m) m i e) = true
  | SmtMap.default T d, i, e, hm, hi, he => by
      exact map_update_aux_no_default_canonical hm hi he (by simp [__smtx_map_entries_ordered_after])
  | SmtMap.cons k v m, i, e, hmCons, hi, he => by
      have hk : value_canonical k := by
        have hParts := hmCons
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        rcases hParts with ⟨hMain, _hNeDefault⟩
        rcases hMain with ⟨hEntries, _hOrdered⟩
        exact hEntries.1.1
      have hv : value_canonical v := by
        have hParts := hmCons
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        rcases hParts with ⟨hMain, _hNeDefault⟩
        rcases hMain with ⟨hEntries, _hOrdered⟩
        exact hEntries.1.2
      have hm : __smtx_map_canonical m = true := by
        have hParts := hmCons
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        rcases hParts with ⟨hMain, _hNeDefault⟩
        rcases hMain with ⟨hEntries, _hOrdered⟩
        exact hEntries.2
      have hOrdTailK : __smtx_map_entries_ordered_after k m = true := by
        have hParts := hmCons
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        rcases hParts with ⟨hMain, _hNeDefault⟩
        exact hMain.2
      have hNeDefault : native_veq v (__smtx_map_get_default m) = false := by
        have hParts := hmCons
        simp [__smtx_map_canonical, SmtEval.native_and, SmtEval.native_not] at hParts
        rcases hParts with ⟨_hMain, hNe⟩
        exact hNe
      cases hEq : native_veq k i
      · cases hLt : native_vcmp k i
        · have hTailCanon :
            __smtx_map_canonical
              (__smtx_map_update_aux (__smtx_map_get_default m) m i e) = true :=
              map_update_aux_canonical_of_order_laws hFlip hTrans hm hi he
          have hOrdUpdated :
              __smtx_map_entries_ordered_after k
                (__smtx_map_update_aux (__smtx_map_get_default m) m i e) = true :=
            map_update_aux_entries_ordered_after hFlip hTrans
              (__smtx_map_get_default m) hm hOrdTailK hEq hLt
          have hDefault :
              __smtx_map_get_default
                (__smtx_map_update_aux (__smtx_map_get_default m) m i e) =
                  __smtx_map_get_default m :=
            map_update_aux_get_default (__smtx_map_get_default m) m i e
          have hkBool : __smtx_value_canonical k = true := by
            simpa [value_canonical] using hk
          have hvBool : __smtx_value_canonical v = true := by
            simpa [value_canonical] using hv
          simp [__smtx_map_update_aux, __smtx_map_get_default, native_ite, hEq,
            hLt, __smtx_map_canonical, hkBool, hvBool, hTailCanon,
            hOrdUpdated, hDefault, hNeDefault,
            SmtEval.native_and, SmtEval.native_not]
        · simpa [__smtx_map_update_aux, native_ite, hEq, hLt] using
            map_update_aux_no_default_canonical hmCons hi he
              (by simpa [__smtx_map_entries_ordered_after] using hLt)
      · have hki : k = i := eq_of_native_veq_true hEq
        subst i
        simpa [__smtx_map_update_aux, native_ite, hEq, __smtx_map_get_default] using
          map_update_aux_no_default_canonical hm hi he hOrdTailK

/-- Canonicality of the recursive map update under the `native_vcmp` order laws. -/
theorem map_update_aux_canonical
    {m : SmtMap}
    {i e : SmtValue}
    (hm : __smtx_map_canonical m = true)
    (hi : value_canonical i)
    (he : value_canonical e) :
    __smtx_map_canonical
      (__smtx_map_update_aux (__smtx_map_get_default m) m i e) = true :=
  map_update_aux_canonical_of_order_laws
    (fun hNe hCmp => native_vcmp_flip hNe hCmp)
    (fun hAB hBC => native_vcmp_trans hAB hBC)
    hm hi he

/--
If all entries in a canonical map are strictly below `i`, lookup at `i` falls
through to the map default.
-/
theorem map_lookup_eq_default_of_entries_ordered_after :
    ∀ {m : SmtMap} {i : SmtValue},
      __smtx_map_canonical m = true ->
        __smtx_map_entries_ordered_after i m = true ->
          __smtx_map_lookup m i = __smtx_map_get_default m
  | SmtMap.default T e, i, _hm, _hOrd => by
      simp [__smtx_map_lookup, __smtx_map_get_default]
  | SmtMap.cons k v m, i, hmCons, hOrd => by
      have hki : native_veq k i = false := native_vcmp_ne hOrd
      have hm : __smtx_map_canonical m = true := by
        have hParts := hmCons
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        rcases hParts with ⟨hMain, _hNeDefault⟩
        rcases hMain with ⟨hEntries, _hOrdered⟩
        exact hEntries.2
      have hOrdTailK : __smtx_map_entries_ordered_after k m = true := by
        have hParts := hmCons
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        rcases hParts with ⟨hMain, _hNeDefault⟩
        exact hMain.2
      have hOrdTailI : __smtx_map_entries_ordered_after i m = true :=
        map_entries_ordered_after_trans
          (fun hAB hBC => native_vcmp_trans hAB hBC) hm hOrdTailK hOrd
      simpa [__smtx_map_lookup, __smtx_map_get_default, native_ite, hki] using
        map_lookup_eq_default_of_entries_ordered_after hm hOrdTailI

/--
The one-step update helper returns the inserted value at the inserted key,
provided the insertion point is ordered with respect to the tail.
-/
theorem map_lookup_update_aux_no_default_same
    {m : SmtMap}
    {i e : SmtValue}
    (hm : __smtx_map_canonical m = true)
    (hOrd : __smtx_map_entries_ordered_after i m = true) :
    __smtx_map_lookup
      (__smtx_map_update_aux_no_default (__smtx_map_get_default m) m i e) i = e := by
  cases hEq : native_veq (__smtx_map_get_default m) e
  · have hii : native_veq i i = true := by
      simp [native_veq]
    simp [__smtx_map_update_aux_no_default, __smtx_map_lookup, native_ite,
      hEq, hii]
  · have hDefaultEq : __smtx_map_get_default m = e := eq_of_native_veq_true hEq
    have hLookup : __smtx_map_lookup m i = e := by
      simpa [hDefaultEq] using
        map_lookup_eq_default_of_entries_ordered_after hm hOrd
    simpa [__smtx_map_update_aux_no_default, native_ite, hEq] using hLookup

/--
The one-step update helper does not change lookup at a distinct key.
-/
theorem map_lookup_update_aux_no_default_other
    (ed : SmtValue)
    (m : SmtMap)
    {i j e : SmtValue}
    (hij : native_veq i j = false) :
    __smtx_map_lookup (__smtx_map_update_aux_no_default ed m i e) j =
      __smtx_map_lookup m j := by
  cases hEq : native_veq ed e <;>
    simp [__smtx_map_update_aux_no_default, __smtx_map_lookup, native_ite,
      hEq, hij]

/--
Looking up the just-updated index in a canonical map returns the updated value.

This is the key semantic counterpart of `map_update_aux_canonical`: canonicality
rules out duplicate keys hidden in the ordered tail.
-/
theorem map_lookup_update_aux_same
    : ∀ {m : SmtMap} {i e : SmtValue},
      __smtx_map_canonical m = true ->
        __smtx_map_lookup
          (__smtx_map_update_aux (__smtx_map_get_default m) m i e) i = e
  | SmtMap.default T d, i, e, hm => by
      exact map_lookup_update_aux_no_default_same
        (m := SmtMap.default T d) (i := i) (e := e) hm
        (by simp [__smtx_map_entries_ordered_after])
  | SmtMap.cons k v m, i, e, hm => by
      have hmTail : __smtx_map_canonical m = true := by
        have hParts := hm
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        rcases hParts with ⟨hMain, _hNeDefault⟩
        rcases hMain with ⟨hEntries, _hOrdered⟩
        exact hEntries.2
      have hOrdTailK : __smtx_map_entries_ordered_after k m = true := by
        have hParts := hm
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        rcases hParts with ⟨hMain, _hNeDefault⟩
        exact hMain.2
      cases hEq : native_veq k i
      · cases hCmp : native_vcmp k i
        · have hRec :
              __smtx_map_lookup
                (__smtx_map_update_aux (__smtx_map_get_default m) m i e) i = e :=
            map_lookup_update_aux_same (m := m) hmTail
          simpa [__smtx_map_update_aux, __smtx_map_lookup, native_ite,
            __smtx_map_get_default, hEq, hCmp] using hRec
        · simpa [__smtx_map_update_aux, native_ite, hEq, hCmp] using
            map_lookup_update_aux_no_default_same
              (m := SmtMap.cons k v m) (i := i) (e := e) hm
              (by simpa [__smtx_map_entries_ordered_after] using hCmp)
      · have hki : k = i := eq_of_native_veq_true hEq
        subst i
        simpa [__smtx_map_update_aux, native_ite, hEq, __smtx_map_get_default] using
          map_lookup_update_aux_no_default_same
            (m := m) (i := k) (e := e) hmTail hOrdTailK

/--
Updating one canonical-map index preserves lookup at a distinct index.

The proof needs the same sorted-map uniqueness invariant as
`map_lookup_update_aux_same`, plus the `native_vcmp` order laws.
-/
theorem map_lookup_update_aux_other
    : ∀ {m : SmtMap} {i j e : SmtValue},
      __smtx_map_canonical m = true ->
        native_veq i j = false ->
          __smtx_map_lookup
            (__smtx_map_update_aux (__smtx_map_get_default m) m i e) j =
              __smtx_map_lookup m j
  | SmtMap.default T d, i, j, e, _hm, hij => by
      exact map_lookup_update_aux_no_default_other
        (__smtx_map_get_default (SmtMap.default T d)) (SmtMap.default T d)
        (i := i) (j := j) (e := e) hij
  | SmtMap.cons k v m, i, j, e, hm, hij => by
      have hmTail : __smtx_map_canonical m = true := by
        have hParts := hm
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        rcases hParts with ⟨hMain, _hNeDefault⟩
        rcases hMain with ⟨hEntries, _hOrdered⟩
        exact hEntries.2
      cases hEqKI : native_veq k i
      · cases hCmp : native_vcmp k i
        · have hRec :
              __smtx_map_lookup
                  (__smtx_map_update_aux (__smtx_map_get_default m) m i e) j =
                __smtx_map_lookup m j :=
            map_lookup_update_aux_other (m := m) hmTail hij
          cases hEqKJ : native_veq k j <;>
            simp [__smtx_map_update_aux, __smtx_map_lookup, native_ite,
              hEqKI, hCmp, hEqKJ, hRec, __smtx_map_get_default]
        · simpa [__smtx_map_update_aux, native_ite, hEqKI, hCmp] using
            map_lookup_update_aux_no_default_other
              (__smtx_map_get_default (SmtMap.cons k v m)) (SmtMap.cons k v m)
              (i := i) (j := j) (e := e) hij
      · have hki : k = i := eq_of_native_veq_true hEqKI
        subst i
        have hKJ : native_veq k j = false := hij
        have hNoDefault :
            __smtx_map_lookup
                (__smtx_map_update_aux_no_default (__smtx_map_get_default m) m k e) j =
              __smtx_map_lookup m j :=
          map_lookup_update_aux_no_default_other
            (__smtx_map_get_default m) m (i := k) (j := j) (e := e) hKJ
        simpa [__smtx_map_update_aux, __smtx_map_lookup, native_ite,
          hEqKI, hKJ, __smtx_map_get_default] using hNoDefault

/-- Updating the same key twice is lookup-equivalent to the last update. -/
theorem map_lookup_update_aux_overwrite
    {m : SmtMap}
    {i e f x : SmtValue}
    (hm : __smtx_map_canonical m = true)
    (hi : value_canonical i)
    (he : value_canonical e) :
    __smtx_map_lookup
        (__smtx_map_update_aux
          (__smtx_map_get_default
            (__smtx_map_update_aux (__smtx_map_get_default m) m i e))
          (__smtx_map_update_aux (__smtx_map_get_default m) m i e) i f) x =
      __smtx_map_lookup
        (__smtx_map_update_aux (__smtx_map_get_default m) m i f) x := by
  let m' := __smtx_map_update_aux (__smtx_map_get_default m) m i e
  have hm' : __smtx_map_canonical m' = true := by
    simpa [m'] using map_update_aux_canonical (m := m) (i := i) (e := e) hm hi he
  cases hix : native_veq i x
  · calc
      __smtx_map_lookup
          (__smtx_map_update_aux (__smtx_map_get_default m') m' i f) x
          = __smtx_map_lookup m' x := by
            exact map_lookup_update_aux_other (m := m') hm' hix
      _ = __smtx_map_lookup m x := by
            exact map_lookup_update_aux_other (m := m) hm hix
      _ = __smtx_map_lookup
          (__smtx_map_update_aux (__smtx_map_get_default m) m i f) x := by
            exact (map_lookup_update_aux_other (m := m) hm hix).symm
  · have hixEq : i = x := eq_of_native_veq_true hix
    subst x
    calc
      __smtx_map_lookup
          (__smtx_map_update_aux (__smtx_map_get_default m') m' i f) i
          = f := map_lookup_update_aux_same (m := m') hm'
      _ = __smtx_map_lookup
          (__smtx_map_update_aux (__smtx_map_get_default m) m i f) i := by
            exact (map_lookup_update_aux_same (m := m) hm).symm

/-- Updates at distinct keys commute up to lookup equivalence. -/
theorem map_lookup_update_aux_swap
    {m : SmtMap}
    {i j e f x : SmtValue}
    (hm : __smtx_map_canonical m = true)
    (hi : value_canonical i)
    (hj : value_canonical j)
    (he : value_canonical e)
    (hf : value_canonical f)
    (hij : native_veq i j = false) :
    __smtx_map_lookup
        (__smtx_map_update_aux
          (__smtx_map_get_default
            (__smtx_map_update_aux (__smtx_map_get_default m) m i e))
          (__smtx_map_update_aux (__smtx_map_get_default m) m i e) j f) x =
      __smtx_map_lookup
        (__smtx_map_update_aux
          (__smtx_map_get_default
            (__smtx_map_update_aux (__smtx_map_get_default m) m j f))
          (__smtx_map_update_aux (__smtx_map_get_default m) m j f) i e) x := by
  let mi := __smtx_map_update_aux (__smtx_map_get_default m) m i e
  let mj := __smtx_map_update_aux (__smtx_map_get_default m) m j f
  have hmi : __smtx_map_canonical mi = true := by
    simpa [mi] using map_update_aux_canonical (m := m) (i := i) (e := e) hm hi he
  have hmj : __smtx_map_canonical mj = true := by
    simpa [mj] using map_update_aux_canonical (m := m) (i := j) (e := f) hm hj hf
  cases hjx : native_veq j x
  · cases hix : native_veq i x
    · calc
        __smtx_map_lookup
            (__smtx_map_update_aux (__smtx_map_get_default mi) mi j f) x
            = __smtx_map_lookup mi x := by
              exact map_lookup_update_aux_other (m := mi) hmi hjx
        _ = __smtx_map_lookup m x := by
              exact map_lookup_update_aux_other (m := m) hm hix
        _ = __smtx_map_lookup mj x := by
              exact (map_lookup_update_aux_other (m := m) hm hjx).symm
        _ = __smtx_map_lookup
            (__smtx_map_update_aux (__smtx_map_get_default mj) mj i e) x := by
              exact (map_lookup_update_aux_other (m := mj) hmj hix).symm
    · have hixEq : i = x := eq_of_native_veq_true hix
      subst x
      have hji : native_veq j i = false := native_veq_false_symm hij
      calc
        __smtx_map_lookup
            (__smtx_map_update_aux (__smtx_map_get_default mi) mi j f) i
            = __smtx_map_lookup mi i := by
              exact map_lookup_update_aux_other (m := mi) hmi hji
        _ = e := map_lookup_update_aux_same (m := m) hm
        _ = __smtx_map_lookup
            (__smtx_map_update_aux (__smtx_map_get_default mj) mj i e) i := by
              exact (map_lookup_update_aux_same (m := mj) hmj).symm
  · have hjxEq : j = x := eq_of_native_veq_true hjx
    subst x
    calc
      __smtx_map_lookup
          (__smtx_map_update_aux (__smtx_map_get_default mi) mi j f) j
          = f := map_lookup_update_aux_same (m := mi) hmi
      _ = __smtx_map_lookup mj j := by
            exact (map_lookup_update_aux_same (m := m) hm).symm
      _ = __smtx_map_lookup
          (__smtx_map_update_aux (__smtx_map_get_default mj) mj i e) j := by
            exact (map_lookup_update_aux_other (m := mj) hmj hij).symm

/-- Updating a key with its current lookup value is lookup-equivalent to no update. -/
theorem map_lookup_update_aux_self
    {m : SmtMap}
    {i x : SmtValue}
    (hm : __smtx_map_canonical m = true) :
    __smtx_map_lookup
        (__smtx_map_update_aux (__smtx_map_get_default m) m i
          (__smtx_map_lookup m i)) x =
      __smtx_map_lookup m x := by
  cases hix : native_veq i x
  · exact map_lookup_update_aux_other (m := m) hm hix
  · have hixEq : i = x := eq_of_native_veq_true hix
    subst x
    exact map_lookup_update_aux_same (m := m) hm

/--
Canonical finite maps with the same default leaf are structurally equal when
all lookups agree.

The default leaf hypothesis is necessary because lookup cannot observe the type
tag stored in `SmtMap.default`.
-/
theorem map_ext_of_lookup_eq :
    ∀ {m1 m2 : SmtMap},
      __smtx_map_canonical m1 = true ->
        __smtx_map_canonical m2 = true ->
          smt_map_default_leaf m1 = smt_map_default_leaf m2 ->
            (∀ v : SmtValue, __smtx_map_lookup m1 v = __smtx_map_lookup m2 v) ->
              m1 = m2
  | SmtMap.default T1 e1, SmtMap.default T2 e2, _hm1, _hm2, hDef, _hLookup => by
      simpa [smt_map_default_leaf] using hDef
  | SmtMap.default T1 e1, SmtMap.cons j f n, _hm1, hm2, hDef, hLookup => by
      have hNeDefault : native_veq f (__smtx_map_get_default n) = false := by
        have hParts := hm2
        simp [__smtx_map_canonical, SmtEval.native_and, SmtEval.native_not] at hParts
        exact hParts.2
      have hDefaultValue : e1 = __smtx_map_get_default n := by
        have hGet := congrArg __smtx_map_get_default hDef
        simpa [smt_map_default_leaf, __smtx_map_get_default,
          map_default_leaf_get_default] using hGet
      have hLookupJ : e1 = f := by
        have hJJ : native_veq j j = true := by
          simp [native_veq]
        simpa [__smtx_map_lookup, native_ite, hJJ] using hLookup j
      have hFDefault : f = __smtx_map_get_default n := hLookupJ ▸ hDefaultValue
      have hVeq : native_veq f (__smtx_map_get_default n) = true := by
        simp [native_veq, hFDefault]
      rw [hVeq] at hNeDefault
      cases hNeDefault
  | SmtMap.cons i e m, SmtMap.default T2 e2, hm1, _hm2, hDef, hLookup => by
      have hNeDefault : native_veq e (__smtx_map_get_default m) = false := by
        have hParts := hm1
        simp [__smtx_map_canonical, SmtEval.native_and, SmtEval.native_not] at hParts
        exact hParts.2
      have hDefaultValue : __smtx_map_get_default m = e2 := by
        have hGet := congrArg __smtx_map_get_default hDef
        simpa [smt_map_default_leaf, __smtx_map_get_default,
          map_default_leaf_get_default] using hGet
      have hLookupI : e = e2 := by
        have hII : native_veq i i = true := by
          simp [native_veq]
        simpa [__smtx_map_lookup, native_ite, hII] using hLookup i
      have hEDefault : e = __smtx_map_get_default m := hLookupI.trans hDefaultValue.symm
      have hVeq : native_veq e (__smtx_map_get_default m) = true := by
        simp [native_veq, hEDefault]
      rw [hVeq] at hNeDefault
      cases hNeDefault
  | SmtMap.cons i e m, SmtMap.cons j f n, hm1, hm2, hDef, hLookup => by
      have hiCanon : value_canonical i := by
        have hParts := hm1
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        exact hParts.1.1.1.1
      have heCanon : value_canonical e := by
        have hParts := hm1
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        exact hParts.1.1.1.2
      have hm : __smtx_map_canonical m = true := by
        have hParts := hm1
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        exact hParts.1.1.2
      have hOrdM : __smtx_map_entries_ordered_after i m = true := by
        have hParts := hm1
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        exact hParts.1.2
      have hNeM : native_veq e (__smtx_map_get_default m) = false := by
        have hParts := hm1
        simp [__smtx_map_canonical, SmtEval.native_and, SmtEval.native_not] at hParts
        exact hParts.2
      have hjCanon : value_canonical j := by
        have hParts := hm2
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        exact hParts.1.1.1.1
      have hfCanon : value_canonical f := by
        have hParts := hm2
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        exact hParts.1.1.1.2
      have hn : __smtx_map_canonical n = true := by
        have hParts := hm2
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        exact hParts.1.1.2
      have hOrdN : __smtx_map_entries_ordered_after j n = true := by
        have hParts := hm2
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        exact hParts.1.2
      have hNeN : native_veq f (__smtx_map_get_default n) = false := by
        have hParts := hm2
        simp [__smtx_map_canonical, SmtEval.native_and, SmtEval.native_not] at hParts
        exact hParts.2
      have hDefTail : smt_map_default_leaf m = smt_map_default_leaf n := by
        simpa [smt_map_default_leaf] using hDef
      have hDefaultValue : __smtx_map_get_default m = __smtx_map_get_default n := by
        have hGet := congrArg __smtx_map_get_default hDefTail
        simpa [map_default_leaf_get_default] using hGet
      cases hij : native_veq i j
      · cases hji : native_vcmp j i
        · have hjiNe : native_veq j i = false := native_veq_false_symm hij
          have hijCmp : native_vcmp i j = true := native_vcmp_flip hjiNe hji
          have hLookupJ := hLookup j
          have hJJ : native_veq j j = true := by
            simp [native_veq]
          have hLeftDefault :
              __smtx_map_lookup (SmtMap.cons i e m) j = __smtx_map_get_default m :=
            map_lookup_eq_default_of_entries_ordered_after
              (m := SmtMap.cons i e m) hm1
              (by simpa [__smtx_map_entries_ordered_after] using hijCmp)
          have hRightJ :
              __smtx_map_lookup (SmtMap.cons j f n) j = f := by
            simp [__smtx_map_lookup, native_ite, hJJ]
          have hFDefaultM : f = __smtx_map_get_default m := by
            exact hRightJ.symm.trans (hLookupJ.symm.trans hLeftDefault)
          have hFDefaultN : f = __smtx_map_get_default n :=
            hFDefaultM.trans hDefaultValue
          have hVeq : native_veq f (__smtx_map_get_default n) = true := by
            simp [native_veq, hFDefaultN]
          rw [hVeq] at hNeN
          cases hNeN
        · have hLookupI := hLookup i
          have hII : native_veq i i = true := by
            simp [native_veq]
          have hjiNe : native_veq j i = false := native_veq_false_symm hij
          have hLeftI :
              __smtx_map_lookup (SmtMap.cons i e m) i = e := by
            simp [__smtx_map_lookup, native_ite, hII]
          have hRightDefault :
              __smtx_map_lookup (SmtMap.cons j f n) i = __smtx_map_get_default n :=
            map_lookup_eq_default_of_entries_ordered_after
              (m := SmtMap.cons j f n) hm2
              (by simpa [__smtx_map_entries_ordered_after] using hji)
          have hEDefaultN : e = __smtx_map_get_default n := by
            exact hLeftI.symm.trans (hLookupI.trans hRightDefault)
          have hEDefaultM : e = __smtx_map_get_default m :=
            hEDefaultN.trans hDefaultValue.symm
          have hVeq : native_veq e (__smtx_map_get_default m) = true := by
            simp [native_veq, hEDefaultM]
          rw [hVeq] at hNeM
          cases hNeM
      · have hijEq : i = j := eq_of_native_veq_true hij
        subst j
        have hII : native_veq i i = true := by
          simp [native_veq]
        have hVal : e = f := by
          simpa [__smtx_map_lookup, native_ite, hII] using hLookup i
        subst f
        have hTailLookup :
            ∀ v : SmtValue, __smtx_map_lookup m v = __smtx_map_lookup n v := by
          intro v
          cases hiv : native_veq i v
          · have hV := hLookup v
            simpa [__smtx_map_lookup, native_ite, hiv] using hV
          · have hivEq : i = v := eq_of_native_veq_true hiv
            subst v
            calc
              __smtx_map_lookup m i = __smtx_map_get_default m :=
                map_lookup_eq_default_of_entries_ordered_after (m := m) hm hOrdM
              _ = __smtx_map_get_default n := hDefaultValue
              _ = __smtx_map_lookup n i :=
                (map_lookup_eq_default_of_entries_ordered_after (m := n) hn hOrdN).symm
        have hTailEq : m = n :=
          map_ext_of_lookup_eq hm hn hDefTail hTailLookup
        subst n
        rfl

/-- Selecting from a canonical map value returns a canonical value. -/
theorem model_eval_select_canonical_of_map
    {m : SmtMap}
    {i : SmtValue}
    (hm : __smtx_map_canonical m = true) :
    value_canonical
      (__smtx_model_eval_select (SmtValue.Map m) i) := by
  simpa [__smtx_model_eval_select, __smtx_map_select] using
    map_lookup_value_canonical (m := m) (i := i) hm

/-- Selecting from a canonical set value returns a canonical value. -/
theorem model_eval_select_canonical_of_set
    {m : SmtMap}
    {i : SmtValue}
    (hm : __smtx_map_canonical m = true) :
    value_canonical
      (__smtx_model_eval_select (SmtValue.Set m) i) := by
  simpa [__smtx_model_eval_select, __smtx_map_select] using
    map_lookup_value_canonical (m := m) (i := i) hm

/-- Value-level select preserves canonicality of its map/set argument. -/
theorem model_eval_select_canonical
    {v i : SmtValue}
    (hv : value_canonical v) :
    value_canonical (__smtx_model_eval_select v i) := by
  cases v <;>
    try
      simpa [__smtx_model_eval_select, __smtx_map_select] using
        value_canonical_notValue
  · have hm : __smtx_map_canonical ‹SmtMap› = true := by
      simpa [value_canonical, __smtx_value_canonical] using hv
    exact model_eval_select_canonical_of_map (m := ‹SmtMap›) (i := i) hm
  · have hm : __smtx_map_canonical ‹SmtMap› = true := by
      have hParts := hv
      simp [value_canonical, __smtx_value_canonical,
        SmtEval.native_and] at hParts
      exact hParts.1
    exact model_eval_select_canonical_of_set (m := ‹SmtMap›) (i := i) hm

end Smtm
