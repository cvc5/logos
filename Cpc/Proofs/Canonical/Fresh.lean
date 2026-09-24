module

public import Cpc.Proofs.Canonical.TypeDefaultBasic
import all Cpc.Proofs.Canonical.TypeDefaultBasic
public import Cpc.Proofs.Canonical.Pump
import all Cpc.Proofs.Canonical.Pump

public section

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Smtm

/-!
Fresh typed canonical values for infinite types, against the declaration-based
datatype definitions and the `__smtx_type_bounded` finiteness fixpoint.

All non-datatype witnesses are discharged directly; the two datatype facts —
the infinite-datatype pump (`infinite_datatype_large_witness`) and the
finite-non-unit non-default witness
(`finite_nonunit_datatype_nondefault_value`) — are supplied by
`Cpc.Proofs.Canonical.Pump`.

The consumed deliverable is `fresh_default_lookup_for_infinite_map_domain`,
used by array extensionality (`RuleSupport.ArraySupport`).
-/

-- === basic helpers ===

private def smt_map_keys : SmtMap -> List SmtValue
  | SmtMap.cons i _ m => i :: smt_map_keys m
  | SmtMap.default _ _ => []

private theorem native_veq_eq_false_of_ne {a b : SmtValue} (h : a ≠ b) :
    native_veq a b = false := by
  simp [native_veq, h]

private theorem native_veq_false_symm {a b : SmtValue}
    (h : native_veq a b = false) :
    native_veq b a = false := by
  simp [native_veq] at h ⊢
  intro hEq
  exact h hEq.symm

private theorem type_default_typed_canonical
    {T : SmtType}
    (hInh : native_inhabited_type T = true)
    (hRec : __smtx_type_wf_rec T = true) :
    __smtx_typeof_value (__smtx_type_default T) = T ∧
      __smtx_value_canonical (__smtx_type_default T) = true :=
  type_default_kernel T hInh hRec

private theorem ne_none_of_native_inhabited {T : SmtType}
    (h : native_inhabited_type T = true) : T ≠ SmtType.None := by
  intro hN
  subst T
  simp [native_inhabited_type, native_Teq, native_not, native_and] at h

private theorem type_default_ne_notValue_of_native_inhabited
    {T : SmtType}
    (hInh : native_inhabited_type T = true) :
    __smtx_type_default T ≠ SmtValue.NotValue := by
  intro hEq
  have hTy := type_default_typed_of_inhabited T hInh
  rw [hEq] at hTy
  simp [__smtx_typeof_value] at hTy
  exact ne_none_of_native_inhabited hInh hTy.symm

-- === finiteness / unit-type unfolding on containers ===

private theorem is_finite_map_eq (T U : SmtType) :
    __smtx_is_finite_type (SmtType.Map T U) =
      native_or (__smtx_is_unit_type U)
        (native_and (__smtx_is_finite_type T) (__smtx_is_finite_type U)) := by
  simp [__smtx_is_finite_type, __smtx_is_unit_type, __smtx_type_bounded,
    native_and, native_not]

private theorem is_finite_set_eq (T : SmtType) :
    __smtx_is_finite_type (SmtType.Set T) = __smtx_is_finite_type T := by
  simp [__smtx_is_finite_type, __smtx_type_bounded, native_and, native_not]

private theorem is_unit_map_eq (T U : SmtType) :
    __smtx_is_unit_type (SmtType.Map T U) = __smtx_is_unit_type U := by
  simp [__smtx_is_unit_type, __smtx_type_bounded, native_or, native_and,
    native_not]

private theorem is_unit_bitvec_eq (w : Nat) :
    __smtx_is_unit_type (SmtType.BitVec w) = native_nateq w 0 := by
  simp [__smtx_is_unit_type, __smtx_type_bounded, native_or, native_not,
    native_nateq]

-- === portable witnesses: numeral / rational / usort / size bounds ===

private def fresh_numeral_index : List SmtValue -> Nat
  | [] => 0
  | SmtValue.Numeral n :: xs => Nat.max (Int.toNat n + 1) (fresh_numeral_index xs)
  | _ :: xs => fresh_numeral_index xs

private theorem fresh_numeral_index_gt_of_mem :
    ∀ {xs : List SmtValue} {n : native_Int},
      SmtValue.Numeral n ∈ xs ->
        Int.toNat n < fresh_numeral_index xs := by
  intro xs
  induction xs with
  | nil =>
      intro n h
      cases h
  | cons v xs ih =>
      intro n h
      cases v <;> simp [fresh_numeral_index] at h ⊢
      case Numeral m =>
        rcases h with hEq | hTail
        · subst n
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
        · exact Nat.lt_of_lt_of_le (ih hTail) (Nat.le_max_right _ _)
      all_goals
        exact ih h

private theorem fresh_numeral_not_mem (xs : List SmtValue) :
    SmtValue.Numeral (Int.ofNat (fresh_numeral_index xs)) ∉ xs := by
  intro h
  have hlt := fresh_numeral_index_gt_of_mem
    (xs := xs) (n := Int.ofNat (fresh_numeral_index xs)) h
  simp at hlt

private theorem fresh_numeral_veq_false_of_mem (xs : List SmtValue) :
    ∀ j : SmtValue, j ∈ xs ->
      native_veq j (SmtValue.Numeral (Int.ofNat (fresh_numeral_index xs))) = false := by
  intro j hj
  exact native_veq_eq_false_of_ne (by
    intro hEq
    subst j
    exact fresh_numeral_not_mem xs hj)

private def fresh_rational_index : List SmtValue -> Nat
  | [] => 0
  | SmtValue.Rational q :: xs => Nat.max (Int.toNat (Rat.floor q) + 1) (fresh_rational_index xs)
  | _ :: xs => fresh_rational_index xs

private theorem fresh_rational_index_gt_of_mem :
    ∀ {xs : List SmtValue} {q : native_Rat},
      SmtValue.Rational q ∈ xs ->
        Int.toNat (Rat.floor q) < fresh_rational_index xs := by
  intro xs
  induction xs with
  | nil =>
      intro q h
      cases h
  | cons v xs ih =>
      intro q h
      cases v <;> simp [fresh_rational_index] at h ⊢
      case Rational r =>
        rcases h with hEq | hTail
        · subst q
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
        · exact Nat.lt_of_lt_of_le (ih hTail) (Nat.le_max_right _ _)
      all_goals
        exact ih h

private theorem fresh_rational_not_mem (xs : List SmtValue) :
    SmtValue.Rational (Int.ofNat (fresh_rational_index xs)) ∉ xs := by
  intro h
  have hlt := fresh_rational_index_gt_of_mem
    (xs := xs) (q := (Int.ofNat (fresh_rational_index xs) : native_Rat)) h
  simp at hlt

private theorem fresh_rational_veq_false_of_mem (xs : List SmtValue) :
    ∀ j : SmtValue, j ∈ xs ->
      native_veq j
        (SmtValue.Rational (Int.ofNat (fresh_rational_index xs))) = false := by
  intro j hj
  exact native_veq_eq_false_of_ne (by
    intro hEq
    subst j
    exact fresh_rational_not_mem xs hj)

private def fresh_usort_index (sort : native_Nat) : List SmtValue -> Nat
  | [] => 0
  | SmtValue.UValue i n :: xs =>
      if i = sort then Nat.max (n + 1) (fresh_usort_index sort xs)
      else fresh_usort_index sort xs
  | _ :: xs => fresh_usort_index sort xs

private theorem fresh_usort_index_gt_of_mem (sort : native_Nat) :
    ∀ {xs : List SmtValue} {n : native_Nat},
      SmtValue.UValue sort n ∈ xs ->
        n < fresh_usort_index sort xs := by
  intro xs
  induction xs with
  | nil =>
      intro n h
      cases h
  | cons v xs ih =>
      intro n h
      cases v
      case UValue i m =>
        by_cases hi : i = sort
        · subst i
          simp [fresh_usort_index] at h ⊢
          rcases h with hEq | hTail
          · subst n
            exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
          · exact Nat.lt_of_lt_of_le (ih hTail) (Nat.le_max_right _ _)
        · have hNe : sort ≠ i := fun hEq => hi hEq.symm
          simp [fresh_usort_index, hi, hNe] at h ⊢
          exact ih h
      all_goals
        simp [fresh_usort_index] at h ⊢
        exact ih h

private theorem fresh_usort_not_mem (sort : native_Nat) (xs : List SmtValue) :
    SmtValue.UValue sort (fresh_usort_index sort xs) ∉ xs := by
  intro h
  have hlt := fresh_usort_index_gt_of_mem sort
    (xs := xs) (n := fresh_usort_index sort xs) h
  exact Nat.lt_irrefl _ hlt

private theorem fresh_usort_veq_false_of_mem (sort : native_Nat) (xs : List SmtValue) :
    ∀ j : SmtValue, j ∈ xs ->
      native_veq j (SmtValue.UValue sort (fresh_usort_index sort xs)) = false := by
  intro j hj
  exact native_veq_eq_false_of_ne (by
    intro hEq
    subst j
    exact fresh_usort_not_mem sort xs hj)

private noncomputable def smt_value_size_bound : List SmtValue -> Nat
  | [] => 0
  | v :: vs => Nat.max (sizeOf v + 1) (smt_value_size_bound vs)

private theorem smt_value_size_lt_bound_of_mem :
    ∀ {xs : List SmtValue} {v : SmtValue},
      v ∈ xs -> sizeOf v < smt_value_size_bound xs := by
  intro xs
  induction xs with
  | nil =>
      intro v h
      cases h
  | cons x xs ih =>
      intro v h
      simp [smt_value_size_bound] at h ⊢
      rcases h with hEq | hTail
      · subst v
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (ih hTail) (Nat.le_max_right _ _)

private theorem native_veq_false_of_mem_and_size_bound
    {xs : List SmtValue}
    {j i : SmtValue}
    (hj : j ∈ xs)
    (hi : smt_value_size_bound xs ≤ sizeOf i) :
    native_veq j i = false := by
  exact native_veq_eq_false_of_ne (by
    intro hEq
    subst i
    have hLt := smt_value_size_lt_bound_of_mem (xs := xs) hj
    exact Nat.not_lt_of_ge hi hLt)

-- === portable seq witnesses ===

private def smt_seq_repeat (T : SmtType) (x : SmtValue) : Nat -> SmtSeq
  | 0 => SmtSeq.empty T
  | Nat.succ n => SmtSeq.cons x (smt_seq_repeat T x n)

private theorem smt_seq_repeat_typeof
    (T : SmtType) (x : SmtValue) (hx : __smtx_typeof_value x = T) :
    ∀ n : Nat,
      __smtx_typeof_seq_value (smt_seq_repeat T x n) = SmtType.Seq T
  | 0 => by
      simp [smt_seq_repeat, __smtx_typeof_seq_value]
  | Nat.succ n => by
      simp [smt_seq_repeat, __smtx_typeof_seq_value,
        smt_seq_repeat_typeof T x hx n, hx, native_ite, native_Teq]

private theorem smt_seq_repeat_canonical
    (T : SmtType) (x : SmtValue) (hx : __smtx_value_canonical x = true) :
    ∀ n : Nat,
      __smtx_seq_canonical (smt_seq_repeat T x n) = true
  | 0 => by
      simp [smt_seq_repeat, __smtx_seq_canonical]
  | Nat.succ n => by
      simp [smt_seq_repeat, __smtx_seq_canonical, native_and, hx,
        smt_seq_repeat_canonical T x hx n]

private theorem smt_seq_repeat_size_ge
    (T : SmtType) (x : SmtValue) :
    ∀ n : Nat, n ≤ sizeOf (smt_seq_repeat T x n)
  | 0 => Nat.zero_le _
  | Nat.succ n => by
      have hRec := smt_seq_repeat_size_ge T x n
      rw [show smt_seq_repeat T x (Nat.succ n) =
        SmtSeq.cons x (smt_seq_repeat T x n) by rfl]
      rw [show sizeOf (SmtSeq.cons x (smt_seq_repeat T x n)) =
        1 + sizeOf x + sizeOf (smt_seq_repeat T x n) by rfl]
      omega

/--
A sequence type over any inhabited well-formed element type has typed
canonical values of arbitrarily large size: repeat the default element.
-/
private theorem seq_inhabited_large_witness
    (T : SmtType)
    (hInh : native_inhabited_type T = true)
    (hRec : __smtx_type_wf_rec T = true)
    (minSize : Nat) :
    ∃ i : SmtValue,
      __smtx_typeof_value i = SmtType.Seq T ∧
        __smtx_value_canonical i = true ∧
          minSize ≤ sizeOf i := by
  have hDef := type_default_typed_canonical hInh hRec
  refine
    ⟨SmtValue.Seq (smt_seq_repeat T (__smtx_type_default T) minSize),
      ?_, ?_, ?_⟩
  · simpa [__smtx_typeof_value] using
      smt_seq_repeat_typeof T (__smtx_type_default T) hDef.1 minSize
  · simpa [__smtx_value_canonical] using
      smt_seq_repeat_canonical T (__smtx_type_default T) hDef.2 minSize
  · rw [show
      sizeOf
          (SmtValue.Seq (smt_seq_repeat T (__smtx_type_default T) minSize)) =
        1 + sizeOf (smt_seq_repeat T (__smtx_type_default T) minSize) by rfl]
    have := smt_seq_repeat_size_ge T (__smtx_type_default T) minSize
    omega

-- === portable map/set head-key/value helpers ===

private def smt_set_head_keys : List SmtValue -> List SmtValue
  | SmtValue.Set (SmtMap.cons k _ _) :: xs => k :: smt_set_head_keys xs
  | _ :: xs => smt_set_head_keys xs
  | [] => []

private theorem smt_set_head_key_mem_of_mem (k e : SmtValue) (m : SmtMap) :
    ∀ {xs : List SmtValue},
      SmtValue.Set (SmtMap.cons k e m) ∈ xs ->
        k ∈ smt_set_head_keys xs := by
  intro xs
  induction xs with
  | nil =>
      intro h
      cases h
  | cons v xs ih =>
      intro h
      cases v <;> simp [smt_set_head_keys] at h ⊢
      case Set m' =>
        cases m' <;> simp [smt_set_head_keys] at h ⊢
        case default T' e' =>
          exact ih h
        case cons k' e' m'' =>
          rcases h with hEq | hTail
          · rcases hEq with ⟨hKey, _hRest⟩
            subst k
            simp
          · exact Or.inr (ih hTail)
      all_goals
        exact ih h

private def smt_map_head_values : List SmtValue -> List SmtValue
  | SmtValue.Map (SmtMap.cons _ e _) :: xs => e :: smt_map_head_values xs
  | _ :: xs => smt_map_head_values xs
  | [] => []

private theorem smt_map_head_value_mem_of_mem (k e : SmtValue) (m : SmtMap) :
    ∀ {xs : List SmtValue},
      SmtValue.Map (SmtMap.cons k e m) ∈ xs ->
        e ∈ smt_map_head_values xs := by
  intro xs
  induction xs with
  | nil =>
      intro h
      cases h
  | cons v xs ih =>
      intro h
      cases v <;> simp [smt_map_head_values] at h ⊢
      case Map m' =>
        cases m' <;> simp [smt_map_head_values] at h ⊢
        case default T' e' =>
          exact ih h
        case cons k' e' m'' =>
          rcases h with hEq | hTail
          · rcases hEq with ⟨_hKey, hValue, _hRest⟩
            subst e
            simp
          · exact Or.inr (ih hTail)
      all_goals
        exact ih h

private def smt_map_head_keys : List SmtValue -> List SmtValue
  | SmtValue.Map (SmtMap.cons k _ _) :: xs => k :: smt_map_head_keys xs
  | _ :: xs => smt_map_head_keys xs
  | [] => []

private theorem smt_map_head_key_mem_of_mem (k e : SmtValue) (m : SmtMap) :
    ∀ {xs : List SmtValue},
      SmtValue.Map (SmtMap.cons k e m) ∈ xs ->
        k ∈ smt_map_head_keys xs := by
  intro xs
  induction xs with
  | nil =>
      intro h
      cases h
  | cons v xs ih =>
      intro h
      cases v <;> simp [smt_map_head_keys] at h ⊢
      case Map m' =>
        cases m' <;> simp [smt_map_head_keys] at h ⊢
        case default T' e' =>
          exact ih h
        case cons k' e' m'' =>
          rcases h with hEq | hTail
          · rcases hEq with ⟨hKey, _hRest⟩
            subst k
            simp
          · exact Or.inr (ih hTail)
      all_goals
        exact ih h

-- === bitvec witnesses ===

private theorem one_mod_pow2_succ (w : Nat) :
    (1 : Int) % (native_int_pow2 (native_nat_to_int (Nat.succ w))) = 1 := by
  have hnot : ¬ ((w : Int) + 1 < 0) := by omega
  have hpow :
      native_int_pow2 (native_nat_to_int (Nat.succ w)) =
        (2 : Int) ^ (Nat.succ w) := by
    simp [native_int_pow2, native_zexp_total, native_nat_to_int, hnot]
  rw [hpow]
  exact Int.emod_eq_of_lt (by decide) (by
    have hNat : (1 : Nat) < 2 ^ Nat.succ w :=
      Nat.one_lt_pow (by simp) (by decide)
    exact_mod_cast hNat)

private theorem one_mod_pow2_succ_zeq (w : Nat) :
    native_zeq (1 : Int)
      (native_mod_total 1 (native_int_pow2 (native_nat_to_int (Nat.succ w)))) = true := by
  simp [native_zeq, native_mod_total, one_mod_pow2_succ]

private theorem bitvec_succ_nonneg (w : Nat) :
    native_zleq 0 (native_nat_to_int (Nat.succ w)) = true := by
  exact decide_eq_true (Int.natCast_nonneg (Nat.succ w))

private theorem bitvec_succ_one_typeof (w : Nat) :
    __smtx_typeof_value
      (SmtValue.Binary (native_nat_to_int (Nat.succ w)) 1) =
        SmtType.BitVec (Nat.succ w) := by
  have hmod := one_mod_pow2_succ_zeq w
  have hnonneg := bitvec_succ_nonneg w
  have htonat : native_int_to_nat (native_nat_to_int (Nat.succ w)) = Nat.succ w := by
    simp [native_int_to_nat, native_nat_to_int]
  simp [__smtx_typeof_value, native_and, native_ite, hmod, hnonneg, htonat]

private theorem bitvec_succ_one_canonical (w : Nat) :
    __smtx_value_canonical
      (SmtValue.Binary (native_nat_to_int (Nat.succ w)) 1) = true := by
  have hmod := one_mod_pow2_succ_zeq w
  have hnonneg := bitvec_succ_nonneg w
  simp [__smtx_value_canonical, native_ite, hmod, hnonneg]

private theorem bitvec_succ_one_ne_default (w : Nat) :
    native_veq
      (SmtValue.Binary (native_nat_to_int (Nat.succ w)) 1)
      (__smtx_type_default (SmtType.BitVec (Nat.succ w))) = false := by
  simp [__smtx_type_default, native_nat_to_int, native_veq]

-- === datatype witnesses (from `Cpc.Proofs.Canonical.Pump`) ===

private theorem infinite_datatype_fresh_value
    (s : native_String) (dd : SmtDatatypeDecl)
    (hInh : native_inhabited_type (SmtType.Datatype s dd) = true)
    (hRec : __smtx_type_wf_rec (SmtType.Datatype s dd) = true)
    (hInfinite : __smtx_is_finite_type (SmtType.Datatype s dd) = false)
    (avoid : List SmtValue) :
    ∃ i : SmtValue,
      __smtx_typeof_value i = SmtType.Datatype s dd ∧
        __smtx_value_canonical i = true ∧
          ∀ j : SmtValue, j ∈ avoid -> native_veq j i = false := by
  rcases infinite_datatype_large_witness (smt_value_size_bound avoid) s dd
      hInh hRec hInfinite with ⟨v, hvTy, hvCan, hvSize⟩
  refine ⟨v, hvTy, hvCan, ?_⟩
  intro j hj
  exact native_veq_false_of_mem_and_size_bound hj hvSize

-- === non-default typed canonical values ===

/--
Every inhabited recursively well-formed non-unit type has a typed canonical
value different from its default.
-/
theorem nonunit_typed_canonical_nondefault_value
    (A : SmtType)
    (_hInh : native_inhabited_type A = true)
    (_hRec : __smtx_type_wf_rec A = true)
    (_hNonUnit : __smtx_is_unit_type A = false) :
    ∃ e : SmtValue,
      __smtx_typeof_value e = A ∧
        __smtx_value_canonical e = true ∧
          native_veq e (__smtx_type_default A) = false := by
  classical
  cases A with
  | None =>
      simp [__smtx_type_wf_rec] at _hRec
  | Bool =>
      refine ⟨SmtValue.Boolean true, ?_, ?_, ?_⟩ <;>
        simp [__smtx_typeof_value, __smtx_value_canonical,
          __smtx_type_default, native_veq]
  | Int =>
      refine ⟨SmtValue.Numeral 1, ?_, ?_, ?_⟩ <;>
        simp [__smtx_typeof_value, __smtx_value_canonical,
          __smtx_type_default, native_veq]
  | Real =>
      refine ⟨SmtValue.Rational (1 : native_Rat), ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value]
      · simp [__smtx_value_canonical]
      · exact native_veq_eq_false_of_ne (by
          simp [__smtx_type_default, native_mk_rational]
          native_decide)
  | RegLan =>
      simp [__smtx_type_wf_rec] at _hRec
  | BitVec w =>
      cases w with
      | zero =>
          rw [is_unit_bitvec_eq] at _hNonUnit
          simp [native_nateq] at _hNonUnit
      | succ w =>
          refine
            ⟨SmtValue.Binary (native_nat_to_int (Nat.succ w)) 1, ?_, ?_, ?_⟩
          · exact bitvec_succ_one_typeof w
          · exact bitvec_succ_one_canonical w
          · exact bitvec_succ_one_ne_default w
  | Map T U =>
      have hRecParts :
          native_inhabited_type T = true ∧
            __smtx_type_wf_rec T = true ∧
              native_inhabited_type U = true ∧
                __smtx_type_wf_rec U = true := by
        have h := _hRec
        simp [__smtx_type_wf_rec, native_and] at h
        exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩
      have hUNonUnit : __smtx_is_unit_type U = false := by
        rw [is_unit_map_eq] at _hNonUnit
        exact _hNonUnit
      have hTDefault :=
        type_default_typed_canonical hRecParts.1 hRecParts.2.1
      have hUDefault :=
        type_default_typed_canonical hRecParts.2.2.1 hRecParts.2.2.2
      rcases nonunit_typed_canonical_nondefault_value
          U hRecParts.2.2.1 hRecParts.2.2.2 hUNonUnit with
        ⟨e, heTy, heCan, heNeDefault⟩
      have heNeDefaultProp : e ≠ __smtx_type_default U := by
        intro hEq
        subst e
        simp [native_veq] at heNeDefault
      have hUNV : __smtx_type_default U ≠ SmtValue.NotValue :=
        type_default_ne_notValue_of_native_inhabited hRecParts.2.2.1
      refine
        ⟨SmtValue.Map
          (SmtMap.cons (__smtx_type_default T) e
            (SmtMap.default T (__smtx_type_default U))), ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value, __smtx_typeof_map_value,
          hTDefault.1, heTy, hUDefault.1, native_ite, native_Teq]
      · simp [__smtx_value_canonical, __smtx_map_canonical,
          __smtx_map_default_canonical, __smtx_map_entries_ordered_after,
          __smtx_map_get_default, hTDefault.2, heCan, hUDefault.1,
          hUDefault.2, heNeDefaultProp, native_and, native_ite, native_not,
          native_veq]
      · rw [show __smtx_type_default (SmtType.Map T U) =
            native_ite (native_veq (__smtx_type_default U) SmtValue.NotValue)
              SmtValue.NotValue
              (SmtValue.Map (SmtMap.default T (__smtx_type_default U))) from by
          simp [__smtx_type_default]]
        simp [native_ite, native_veq, hUNV]
  | Set T =>
      have hRecParts :
          native_inhabited_type T = true ∧
            __smtx_type_wf_rec T = true := by
        have h := _hRec
        simp [__smtx_type_wf_rec, native_and] at h
        exact h
      have hTDefault :=
        type_default_typed_canonical hRecParts.1 hRecParts.2
      refine
        ⟨SmtValue.Set
          (SmtMap.cons (__smtx_type_default T) (SmtValue.Boolean true)
            (SmtMap.default T (SmtValue.Boolean false))), ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value, __smtx_typeof_map_value,
          __smtx_map_to_set_type, hTDefault.1, native_ite, native_Teq]
      · simp [__smtx_value_canonical, __smtx_map_canonical,
          __smtx_map_default_canonical, __smtx_map_entries_ordered_after,
          __smtx_map_get_default, hTDefault.2, native_and, native_ite,
          native_not, native_veq, __smtx_typeof_value, __smtx_type_default]
      · simp [__smtx_type_default, native_veq]
  | Seq T =>
      have hRecParts :
          native_inhabited_type T = true ∧
            __smtx_type_wf_rec T = true := by
        have h := _hRec
        simp [__smtx_type_wf_rec, native_and] at h
        exact h
      have hTDefault :=
        type_default_typed_canonical hRecParts.1 hRecParts.2
      refine
        ⟨SmtValue.Seq (SmtSeq.cons (__smtx_type_default T) (SmtSeq.empty T)),
          ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value, __smtx_typeof_seq_value,
          hTDefault.1, native_ite, native_Teq]
      · simp [__smtx_value_canonical, __smtx_seq_canonical,
          hTDefault.2, native_and]
      · simp [__smtx_type_default, native_veq]
  | Char =>
      refine ⟨SmtValue.Char 1, ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value, native_char_valid, native_ite]
      · simp [__smtx_value_canonical, native_char_valid]
      · simp [__smtx_type_default, native_veq]
  | Datatype s dd =>
      by_cases hFinite :
          __smtx_is_finite_type (SmtType.Datatype s dd) = true
      · exact finite_nonunit_datatype_nondefault_value
          s dd _hInh _hRec hFinite _hNonUnit
      · have hInfinite :
            __smtx_is_finite_type (SmtType.Datatype s dd) = false := by
          cases h : __smtx_is_finite_type (SmtType.Datatype s dd) <;>
            simp [h] at hFinite ⊢
        rcases infinite_datatype_fresh_value
            s dd _hInh _hRec hInfinite
            [__smtx_type_default (SmtType.Datatype s dd)] with
          ⟨e, heTy, heCan, heFresh⟩
        refine ⟨e, heTy, heCan, ?_⟩
        exact native_veq_false_symm
          (heFresh (__smtx_type_default (SmtType.Datatype s dd)) (by simp))
  | TypeRef s =>
      simp [__smtx_type_wf_rec] at _hRec
  | USort u =>
      refine ⟨SmtValue.UValue u 1, ?_, ?_, ?_⟩ <;>
        simp [__smtx_typeof_value, __smtx_value_canonical,
          __smtx_type_default, native_veq]
  | FunType T U =>
      simp [__smtx_type_wf_rec] at _hRec
  | DtcAppType T U =>
      simp [__smtx_type_wf_rec] at _hRec
termination_by sizeOf A

-- === fresh typed canonical value for infinite types ===

/--
Every inhabited recursively well-formed infinite type has a typed canonical
value avoiding any given finite list of values.
-/
theorem fresh_typed_canonical_value_for_infinite_type
    (A : SmtType)
    (_hInh : native_inhabited_type A = true)
    (_hRec : __smtx_type_wf_rec A = true)
    (_hInfinite : __smtx_is_finite_type A = false)
    (avoid : List SmtValue) :
    ∃ i : SmtValue,
      __smtx_typeof_value i = A ∧
        __smtx_value_canonical i = true ∧
          ∀ j : SmtValue, j ∈ avoid -> native_veq j i = false := by
  classical
  cases A with
  | None =>
      simp [__smtx_type_wf_rec] at _hRec
  | Bool =>
      simp [__smtx_is_finite_type, __smtx_type_bounded, native_not]
        at _hInfinite
  | Int =>
      refine ⟨SmtValue.Numeral (Int.ofNat (fresh_numeral_index avoid)), ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value]
      · simp [__smtx_value_canonical]
      · exact fresh_numeral_veq_false_of_mem avoid
  | Real =>
      refine ⟨SmtValue.Rational (Int.ofNat (fresh_rational_index avoid)), ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value]
      · simp [__smtx_value_canonical]
      · exact fresh_rational_veq_false_of_mem avoid
  | RegLan =>
      simp [__smtx_type_wf_rec] at _hRec
  | BitVec w =>
      simp [__smtx_is_finite_type, __smtx_type_bounded, native_or, native_not]
        at _hInfinite
  | Char =>
      simp [__smtx_is_finite_type, __smtx_type_bounded, native_not]
        at _hInfinite
  | Map T U =>
      have hRecParts :
          native_inhabited_type T = true ∧
            __smtx_type_wf_rec T = true ∧
              native_inhabited_type U = true ∧
                __smtx_type_wf_rec U = true := by
        have h := _hRec
        simp [__smtx_type_wf_rec, native_and] at h
        exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩
      have hTDefault :=
        type_default_typed_canonical hRecParts.1 hRecParts.2.1
      have hUDefault :=
        type_default_typed_canonical hRecParts.2.2.1 hRecParts.2.2.2
      by_cases hUInfinite : __smtx_is_finite_type U = false
      · rcases fresh_typed_canonical_value_for_infinite_type
            U hRecParts.2.2.1 hRecParts.2.2.2 hUInfinite
              (__smtx_type_default U :: smt_map_head_values avoid) with
          ⟨e, heTy, heCan, heFresh⟩
        have hDefaultNe : native_veq (__smtx_type_default U) e = false :=
          heFresh (__smtx_type_default U) (by simp)
        have hEntryNe : native_veq e (__smtx_type_default U) = false :=
          native_veq_false_symm hDefaultNe
        have hEntryNeProp : e ≠ __smtx_type_default U := by
          intro hEq
          subst e
          simp [native_veq] at hEntryNe
        refine
          ⟨SmtValue.Map
            (SmtMap.cons (__smtx_type_default T) e
              (SmtMap.default T (__smtx_type_default U))), ?_, ?_, ?_⟩
        · simp [__smtx_typeof_value, __smtx_typeof_map_value,
            hTDefault.1, hUDefault.1, heTy, native_ite, native_Teq]
        · simp [__smtx_value_canonical, __smtx_map_canonical,
            __smtx_map_default_canonical, __smtx_map_entries_ordered_after,
            __smtx_map_get_default, hTDefault.2, hUDefault.1, hUDefault.2,
            heCan, hEntryNeProp, native_and, native_ite, native_not,
            native_veq]
        · intro j hj
          exact native_veq_eq_false_of_ne (by
            intro hEq
            subst j
            have heMem : e ∈ smt_map_head_values avoid :=
              smt_map_head_value_mem_of_mem (__smtx_type_default T) e
                (SmtMap.default T (__smtx_type_default U)) hj
            have heFalse := heFresh e (by simp [heMem])
            simp [native_veq] at heFalse)
      · have hUFinite : __smtx_is_finite_type U = true := by
          cases hUF : __smtx_is_finite_type U <;> simp [hUF] at hUInfinite ⊢
        have hFiniteParts :
            __smtx_is_unit_type U = false ∧
              __smtx_is_finite_type T = false := by
          have h := _hInfinite
          rw [is_finite_map_eq] at h
          cases hUnit : __smtx_is_unit_type U <;>
            cases hTFin : __smtx_is_finite_type T <;>
              simp [hUnit, hTFin, hUFinite, native_or, native_and] at h ⊢
        rcases fresh_typed_canonical_value_for_infinite_type
            T hRecParts.1 hRecParts.2.1 hFiniteParts.2
              (smt_map_head_keys avoid) with
          ⟨k, hkTy, hkCan, hkFresh⟩
        rcases nonunit_typed_canonical_nondefault_value
            U hRecParts.2.2.1 hRecParts.2.2.2 hFiniteParts.1 with
          ⟨e, heTy, heCan, heNeDefault⟩
        have heNeDefaultProp : e ≠ __smtx_type_default U := by
          intro hEq
          subst e
          simp [native_veq] at heNeDefault
        refine
          ⟨SmtValue.Map
            (SmtMap.cons k e
              (SmtMap.default T (__smtx_type_default U))), ?_, ?_, ?_⟩
        · simp [__smtx_typeof_value, __smtx_typeof_map_value,
            hkTy, heTy, hUDefault.1, native_ite, native_Teq]
        · simp [__smtx_value_canonical, __smtx_map_canonical,
            __smtx_map_default_canonical, __smtx_map_entries_ordered_after,
            __smtx_map_get_default, hkCan, heCan, hUDefault.1, hUDefault.2,
            heNeDefaultProp, native_and, native_ite, native_not, native_veq]
        · intro j hj
          exact native_veq_eq_false_of_ne (by
            intro hEq
            subst j
            have hkMem : k ∈ smt_map_head_keys avoid :=
              smt_map_head_key_mem_of_mem k e
                (SmtMap.default T (__smtx_type_default U)) hj
            have hkFalse := hkFresh k hkMem
            simp [native_veq] at hkFalse)
  | Set T =>
      have hRecParts :
          native_inhabited_type T = true ∧
            __smtx_type_wf_rec T = true := by
        have h := _hRec
        simp [__smtx_type_wf_rec, native_and] at h
        exact h
      have hTInfinite : __smtx_is_finite_type T = false := by
        rw [is_finite_set_eq] at _hInfinite
        exact _hInfinite
      rcases fresh_typed_canonical_value_for_infinite_type
          T hRecParts.1 hRecParts.2 hTInfinite (smt_set_head_keys avoid) with
        ⟨x, hxTy, hxCan, hxFresh⟩
      refine
        ⟨SmtValue.Set
          (SmtMap.cons x (SmtValue.Boolean true)
            (SmtMap.default T (SmtValue.Boolean false))), ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value, __smtx_typeof_map_value,
          __smtx_map_to_set_type, hxTy, native_ite, native_Teq]
      · simp [__smtx_value_canonical, __smtx_map_canonical,
          __smtx_map_default_canonical, __smtx_map_entries_ordered_after,
          __smtx_map_get_default, hxCan, native_and, native_ite,
          native_not, native_veq, __smtx_typeof_value, __smtx_type_default]
      · intro j hj
        exact native_veq_eq_false_of_ne (by
          intro hEq
          subst j
          have hxMem : x ∈ smt_set_head_keys avoid :=
            smt_set_head_key_mem_of_mem x (SmtValue.Boolean true)
              (SmtMap.default T (SmtValue.Boolean false)) hj
          have hxFalse := hxFresh x hxMem
          simp [native_veq] at hxFalse)
  | Seq T =>
      have hRecParts :
          native_inhabited_type T = true ∧
            __smtx_type_wf_rec T = true := by
        have h := _hRec
        simp [__smtx_type_wf_rec, native_and] at h
        exact h
      rcases seq_inhabited_large_witness T hRecParts.1 hRecParts.2
          (smt_value_size_bound avoid) with
        ⟨i, hiTy, hiCan, hiSize⟩
      refine ⟨i, hiTy, hiCan, ?_⟩
      intro j hj
      exact native_veq_false_of_mem_and_size_bound hj hiSize
  | Datatype s dd =>
      exact infinite_datatype_fresh_value s dd _hInh _hRec _hInfinite avoid
  | TypeRef s =>
      simp [__smtx_type_wf_rec] at _hRec
  | USort u =>
      refine ⟨SmtValue.UValue u (fresh_usort_index u avoid), ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value]
      · simp [__smtx_value_canonical]
      · exact fresh_usort_veq_false_of_mem u avoid
  | FunType T U =>
      simp [__smtx_type_wf_rec] at _hRec
  | DtcAppType T U =>
      simp [__smtx_type_wf_rec] at _hRec
termination_by sizeOf A

-- === map-lookup freshness + the consumed deliverable ===

private theorem msm_lookup_eq_default_of_fresh_keys :
    ∀ (m : SmtMap) (i : SmtValue),
      (∀ j : SmtValue, j ∈ smt_map_keys m -> native_veq j i = false) ->
        __smtx_map_lookup m i = __smtx_map_get_default m
  | SmtMap.default T e, i, _hFresh => by
      simp [__smtx_map_lookup, __smtx_map_get_default]
  | SmtMap.cons j e m, i, hFresh => by
      have hj : native_veq j i = false := hFresh j (by simp [smt_map_keys])
      have hmFresh :
          ∀ k : SmtValue, k ∈ smt_map_keys m -> native_veq k i = false := by
        intro k hk
        exact hFresh k (by simp [smt_map_keys, hk])
      have hmLookup :
          __smtx_map_lookup m i = __smtx_map_get_default m :=
        msm_lookup_eq_default_of_fresh_keys m i hmFresh
      simpa [smt_map_keys, __smtx_map_lookup, __smtx_map_get_default,
        native_ite, hj] using hmLookup

/--
Fresh-index theorem for infinite map domains.

When the executable map-difference proof needs to compare the two default
payloads of canonical maps over an infinite domain, it needs a typed canonical
index outside both finite spines.
-/
theorem fresh_default_lookup_for_infinite_map_domain
    (m1 m2 : SmtMap)
    (A B : SmtType)
    (_hm1Ty : __smtx_typeof_map_value m1 = SmtType.Map A B)
    (_hm2Ty : __smtx_typeof_map_value m2 = SmtType.Map A B)
    (_hm1Can : __smtx_map_canonical m1 = true)
    (_hm2Can : __smtx_map_canonical m2 = true)
    (hAInh : native_inhabited_type A = true)
    (hARec : __smtx_type_wf_rec A = true)
    (_hInfinite : __smtx_is_finite_type A = false) :
    ∃ i : SmtValue,
      __smtx_typeof_value i = A ∧
        __smtx_value_canonical i = true ∧
          __smtx_map_lookup m1 i = __smtx_map_get_default m1 ∧
            __smtx_map_lookup m2 i = __smtx_map_get_default m2 := by
  rcases fresh_typed_canonical_value_for_infinite_type
      A hAInh hARec _hInfinite (smt_map_keys m1 ++ smt_map_keys m2) with
    ⟨i, hiTy, hiCan, hiFresh⟩
  refine ⟨i, hiTy, hiCan, ?_, ?_⟩
  · exact msm_lookup_eq_default_of_fresh_keys m1 i (by
      intro j hj
      exact hiFresh j (by simp [hj]))
  · exact msm_lookup_eq_default_of_fresh_keys m2 i (by
      intro j hj
      exact hiFresh j (by simp [hj]))

end Smtm
