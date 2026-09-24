module

public import Cpc.Proofs.Canonical.Pump
import all Cpc.Proofs.Canonical.Pump
public import Cpc.Proofs.Canonical.Order
import all Cpc.Proofs.Canonical.Order

public section

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Smtm

/-!
# Soundness of the finiteness and unit-type classifications

The semantic domain of a sort `T` is its set of *typed canonical values*,

  `⟦T⟧ := {v : SmtValue | __smtx_typeof_value v = T ∧
                          __smtx_value_canonical v = true}`,

which is exactly the range of the quantifier evaluators
(`native_eval_exists` / `native_eval_forall` / `native_eval_choice`).
The executable classifiers `__smtx_is_finite_type` and `__smtx_is_unit_type`
(both instances of the `__smtx_type_bounded` fixpoint) are intended to
characterize the cardinality of `⟦T⟧`.  Their correctness decomposes into
four statements, all relative to the guard
`native_inhabited_type T = true ∧ __smtx_type_wf_rec T = true`
(the guard is essential: e.g. a sequence type over an uninhabited element
type has exactly one canonical value even though sequences are classified
infinite, but such a type is not recursively well-formed):

1. **Finite soundness** — `__smtx_is_finite_type T = true` implies `⟦T⟧` is
   finite: there is a list containing every typed canonical value of `T`.
   Proven here: `finite_type_enumerable`.

2. **Finite completeness** — `__smtx_is_finite_type T = false` implies `⟦T⟧`
   is infinite: for every finite avoid-list there is a typed canonical value
   outside it.  Proven in `Cpc.Proofs.Canonical.Fresh`
   (`fresh_typed_canonical_value_for_infinite_type`, built on the
   infinite-datatype pump of `Cpc.Proofs.Canonical.Pump`).

3. **Unit soundness** — `__smtx_is_unit_type T = true` implies `⟦T⟧` is a
   singleton: every typed canonical value of `T` equals
   `__smtx_type_default T`.  Proven here: `unit_type_values_default`.

4. **Unit completeness** — `__smtx_is_unit_type T = false` implies `⟦T⟧` has
   at least two elements: there is a typed canonical value different from
   the default.  Proven in `Cpc.Proofs.Canonical.Fresh`
   (`nonunit_typed_canonical_nondefault_value`).

Together the four statements certify that the classifiers agree exactly with
the semantic cardinalities on the well-formed inhabited domain:
`is_finite T = true ↔ ⟦T⟧ finite` and `is_unit T = true ↔ ⟦T⟧ = {default}`.

Proof structure of this file:
- typed-value *shape inversion*: which value constructors can inhabit a
  given type shape; culminating in constructor-spine inversion for datatype
  types (`chain_typed_spine`).
- statement 3 by structural recursion on the type, with the datatype case
  running the addition-order induction `decl_bounded_payload` over the unit
  fixpoint and identifying the generated default spine slot-by-slot.
- statement 1 by structural recursion on the type, with bounded-length list
  enumeration for maps and sets (this is where the strict-order facts for
  `native_vcmp` from `Cpc.Proofs.Canonical.Order` are needed: canonical map
  entries are adjacently `vcmp`-sorted, and only transitivity plus
  irreflexivity make their keys pairwise distinct, bounding the entry-list
  length by the domain enumeration), and the same addition-order induction
  for datatypes.
-/

-- === shape helpers for `__smtx_typeof_value` ===

private theorem map_to_set_type_shape (X : SmtType) :
    (∃ A : SmtType, __smtx_map_to_set_type X = SmtType.Set A) ∨
      __smtx_map_to_set_type X = SmtType.None := by
  cases X with
  | Map A B =>
      cases B with
      | Bool => exact Or.inl ⟨A, by simp [__smtx_map_to_set_type]⟩
      | _ => right; simp [__smtx_map_to_set_type]
  | _ => right; simp [__smtx_map_to_set_type]

/-- Totality of the constructor-chain type at a given index. -/
private theorem dt_cons_value_rec_cases (T : SmtType) :
    ∀ (d : SmtDatatype) (k : Nat),
      __smtx_typeof_dt_cons_value_rec T d k = SmtType.None ∨
        ∃ c : SmtDatatypeCons,
          dt_nth_cons d k = some c ∧
            __smtx_typeof_dt_cons_value_rec T d k =
              dtc_chain_type T (dtc_fields c)
  | SmtDatatype.null, k => by
      left
      cases k <;> simp [__smtx_typeof_dt_cons_value_rec]
  | SmtDatatype.sum c d, 0 =>
      Or.inr ⟨c, rfl, typeof_dt_cons_value_rec_chain_zero T c d⟩
  | SmtDatatype.sum c d, Nat.succ k => by
      rcases dt_cons_value_rec_cases T d k with h | ⟨c', hnth, h⟩
      · left
        simpa [__smtx_typeof_dt_cons_value_rec] using h
      · right
        exact ⟨c', by simpa [dt_nth_cons] using hnth, by
          simpa [__smtx_typeof_dt_cons_value_rec] using h⟩

/-- A constructor chain is either the bare datatype or a `DtcAppType`. -/
private theorem chain_shape_cases (s : native_String) (dd : SmtDatatypeDecl) :
    ∀ Us : List SmtType,
      (Us = [] ∧
        dtc_chain_type (SmtType.Datatype s dd) Us = SmtType.Datatype s dd) ∨
      (∃ (U : SmtType) (Us' : List SmtType),
        Us = U :: Us' ∧
          dtc_chain_type (SmtType.Datatype s dd) Us =
            SmtType.DtcAppType U
              (dtc_chain_type (SmtType.Datatype s dd) Us'))
  | [] => Or.inl ⟨rfl, rfl⟩
  | U :: Us' => Or.inr ⟨U, Us', rfl, rfl⟩

private theorem chain_ne_none (s : native_String) (dd : SmtDatatypeDecl)
    (Us : List SmtType) :
    dtc_chain_type (SmtType.Datatype s dd) Us ≠ SmtType.None := by
  rcases chain_shape_cases s dd Us with ⟨_, h⟩ | ⟨U, Us', _, h⟩ <;>
    rw [h] <;> intro hEq <;> cases hEq

private theorem chain_inj (s1 : native_String) (d1 : SmtDatatypeDecl)
    (s2 : native_String) (d2 : SmtDatatypeDecl) :
    ∀ (L1 L2 : List SmtType),
      dtc_chain_type (SmtType.Datatype s1 d1) L1 =
        dtc_chain_type (SmtType.Datatype s2 d2) L2 ->
      s1 = s2 ∧ d1 = d2 ∧ L1 = L2
  | [], [], h => by
      simp [dtc_chain_type] at h
      exact ⟨h.1, h.2, rfl⟩
  | [], U :: L2', h => by
      simp [dtc_chain_type] at h
  | U :: L1', [], h => by
      simp [dtc_chain_type] at h
  | U1 :: L1', U2 :: L2', h => by
      simp only [dtc_chain_type] at h
      injection h with hU hRest
      rcases chain_inj s1 d1 s2 d2 L1' L2' hRest with ⟨hs, hd, hL⟩
      exact ⟨hs, hd, by rw [hU, hL]⟩

/-- Inversion of value-level application typing. -/
private theorem apply_value_inversion {X Y Z : SmtType}
    (h : __smtx_typeof_apply_value X Y = Z)
    (hZ : Z ≠ SmtType.None) :
    X = SmtType.DtcAppType Y Z ∧ Y ≠ SmtType.None := by
  cases X with
  | DtcAppType T U =>
      simp only [__smtx_typeof_apply_value, __smtx_typeof_guard] at h
      by_cases hTN : native_Teq T SmtType.None = true
      · rw [native_ite, if_pos hTN] at h
        exact absurd h.symm (by simpa using hZ)
      · rw [native_ite, if_neg hTN] at h
        by_cases hTV : native_Teq T Y = true
        · rw [native_ite, if_pos hTV] at h
          have hTY : T = Y := by simpa [native_Teq] using hTV
          subst T
          subst Z
          refine ⟨rfl, ?_⟩
          intro hYN
          subst Y
          simp [native_Teq] at hTN
        · rw [native_ite, if_neg hTV] at h
          exact absurd h.symm (by simpa using hZ)
  | _ =>
      simp [__smtx_typeof_apply_value] at h
      exact absurd h.symm (by simpa using hZ)

/--
Every value whose type is a `DtcAppType` is a partial constructor
application; in particular the stored result type is a constructor chain.
-/
private theorem typeof_dtcapp_chain :
    ∀ (v : SmtValue) (U rest : SmtType),
      __smtx_typeof_value v = SmtType.DtcAppType U rest ->
      ∃ (s : native_String) (dd : SmtDatatypeDecl) (Us : List SmtType),
        rest = dtc_chain_type (SmtType.Datatype s dd) Us
  | SmtValue.NotValue, U, rest, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.Boolean b, U, rest, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.Numeral n, U, rest, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.Rational q, U, rest, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.Binary w n, U, rest, h => by
      by_cases hc :
          (native_and (native_zleq 0 w)
            (native_zeq n (native_mod_total n (native_int_pow2 w)))) = true <;>
        simp [__smtx_typeof_value, native_ite, hc] at h
  | SmtValue.Map m, U, rest, h => by
      rcases typeof_map_value_shape m with ⟨A, B, hm⟩ | hm <;>
        simp [__smtx_typeof_value, hm] at h
  | SmtValue.Fun i T1 U1, U, rest, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.Set m, U, rest, h => by
      rcases map_to_set_type_shape (__smtx_typeof_map_value m) with
        ⟨A, hm⟩ | hm <;>
        simp [__smtx_typeof_value, hm] at h
  | SmtValue.Seq ss, U, rest, h => by
      rcases typeof_seq_value_shape ss with ⟨A, hs⟩ | hs <;>
        simp [__smtx_typeof_value, hs] at h
  | SmtValue.Char c, U, rest, h => by
      by_cases hc : native_char_valid c = true <;>
        simp [__smtx_typeof_value, native_ite, hc] at h
  | SmtValue.UValue i e, U, rest, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.DtCons s' dd' j, U, rest, h => by
      have hTy :
          __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s' dd')
              (__smtx_dt_resolve (__smtx_dd_lookup s' dd') dd') j =
            SmtType.DtcAppType U rest := by
        simpa [__smtx_typeof_value] using h
      rcases dt_cons_value_rec_cases (SmtType.Datatype s' dd')
          (__smtx_dt_resolve (__smtx_dd_lookup s' dd') dd') j with
        hNone | ⟨c, hnth, hChain⟩
      · rw [hNone] at hTy
        cases hTy
      · rw [hChain] at hTy
        rcases chain_shape_cases s' dd' (dtc_fields c) with
          ⟨hNil, hEq⟩ | ⟨U', Us', hCons, hEq⟩
        · rw [hEq] at hTy
          cases hTy
        · rw [hEq] at hTy
          injection hTy with _ hRest
          exact ⟨s', dd', Us', hRest.symm⟩
  | SmtValue.Apply f a, U, rest, h => by
      have hTy :
          __smtx_typeof_apply_value (__smtx_typeof_value f)
              (__smtx_typeof_value a) =
            SmtType.DtcAppType U rest := by
        simpa [__smtx_typeof_value] using h
      rcases apply_value_inversion hTy (by intro hEq; cases hEq) with ⟨hf, _⟩
      rcases typeof_dtcapp_chain f (__smtx_typeof_value a)
          (SmtType.DtcAppType U rest) hf with ⟨s, dd, Us, hChain⟩
      rcases chain_shape_cases s dd Us with
        ⟨hNil, hEq⟩ | ⟨U', Us', hCons, hEq⟩
      · rw [hEq] at hChain
        cases hChain
      · rw [hEq] at hChain
        injection hChain with _ hRest
        exact ⟨s, dd, Us', hRest⟩

/-- The type of an application value is a constructor chain (or `None`). -/
private theorem apply_result_chain (f a : SmtValue) (Z : SmtType)
    (h : __smtx_typeof_value (SmtValue.Apply f a) = Z)
    (hZ : Z ≠ SmtType.None) :
    ∃ (s : native_String) (dd : SmtDatatypeDecl) (Us : List SmtType),
      Z = dtc_chain_type (SmtType.Datatype s dd) Us := by
  have hTy :
      __smtx_typeof_apply_value (__smtx_typeof_value f)
          (__smtx_typeof_value a) = Z := by
    simpa [__smtx_typeof_value] using h
  rcases apply_value_inversion hTy hZ with ⟨hf, _⟩
  exact typeof_dtcapp_chain f (__smtx_typeof_value a) Z hf

/-- The type of a bare constructor value is a chain (or `None`). -/
private theorem dt_cons_result_chain (s' : native_String)
    (dd' : SmtDatatypeDecl) (j : Nat) (Z : SmtType)
    (h : __smtx_typeof_value (SmtValue.DtCons s' dd' j) = Z)
    (hZ : Z ≠ SmtType.None) :
    ∃ Us : List SmtType,
      Z = dtc_chain_type (SmtType.Datatype s' dd') Us := by
  have hTy :
      __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s' dd')
          (__smtx_dt_resolve (__smtx_dd_lookup s' dd') dd') j = Z := by
    simpa [__smtx_typeof_value] using h
  rcases dt_cons_value_rec_cases (SmtType.Datatype s' dd')
      (__smtx_dt_resolve (__smtx_dd_lookup s' dd') dd') j with
    hNone | ⟨c, hnth, hChain⟩
  · rw [hNone] at hTy
    exact absurd hTy.symm hZ
  · exact ⟨dtc_fields c, by rw [← hTy, hChain]⟩

-- === typed-value shape lemmas ===

private theorem not_chain_of_base {s : native_String} {dd : SmtDatatypeDecl}
    {Us : List SmtType} {X : SmtType}
    (hX : dtc_chain_type (SmtType.Datatype s dd) Us = X)
    (hD : ∀ s' dd', X ≠ SmtType.Datatype s' dd')
    (hA : ∀ U rest, X ≠ SmtType.DtcAppType U rest) : False := by
  rcases chain_shape_cases s dd Us with ⟨_, hEq⟩ | ⟨U, Us', _, hEq⟩
  · rw [hEq] at hX
    exact hD s dd hX.symm
  · rw [hEq] at hX
    exact hA U (dtc_chain_type (SmtType.Datatype s dd) Us') hX.symm

private theorem typed_bool_shape (v : SmtValue)
    (h : __smtx_typeof_value v = SmtType.Bool) :
    ∃ b : native_Bool, v = SmtValue.Boolean b := by
  cases v with
  | Boolean b => exact ⟨b, rfl⟩
  | Binary w n =>
      by_cases hc :
          (native_and (native_zleq 0 w)
            (native_zeq n (native_mod_total n (native_int_pow2 w)))) = true <;>
        simp [__smtx_typeof_value, native_ite, hc] at h
  | Map m =>
      rcases typeof_map_value_shape m with ⟨A, B, hm⟩ | hm <;>
        simp [__smtx_typeof_value, hm] at h
  | Set m =>
      rcases map_to_set_type_shape (__smtx_typeof_map_value m) with
        ⟨A, hm⟩ | hm <;>
        simp [__smtx_typeof_value, hm] at h
  | Seq ss =>
      rcases typeof_seq_value_shape ss with ⟨A, hs⟩ | hs <;>
        simp [__smtx_typeof_value, hs] at h
  | Char c =>
      by_cases hc : native_char_valid c = true <;>
        simp [__smtx_typeof_value, native_ite, hc] at h
  | DtCons s' dd' j =>
      exfalso
      rcases dt_cons_result_chain s' dd' j SmtType.Bool h
          (by intro hEq; cases hEq) with ⟨Us, hChain⟩
      exact not_chain_of_base hChain.symm
        (by intro _ _ hEq; cases hEq) (by intro _ _ hEq; cases hEq)
  | Apply f a =>
      exfalso
      rcases apply_result_chain f a SmtType.Bool h
          (by intro hEq; cases hEq) with ⟨s, dd, Us, hChain⟩
      exact not_chain_of_base hChain.symm
        (by intro _ _ hEq; cases hEq) (by intro _ _ hEq; cases hEq)
  | _ => simp [__smtx_typeof_value] at h

private theorem typed_bitvec_shape (v : SmtValue) (w : Nat)
    (h : __smtx_typeof_value v = SmtType.BitVec w) :
    ∃ (wi n : native_Int), v = SmtValue.Binary wi n := by
  cases v with
  | Binary wi n => exact ⟨wi, n, rfl⟩
  | Map m =>
      rcases typeof_map_value_shape m with ⟨A, B, hm⟩ | hm <;>
        simp [__smtx_typeof_value, hm] at h
  | Set m =>
      rcases map_to_set_type_shape (__smtx_typeof_map_value m) with
        ⟨A, hm⟩ | hm <;>
        simp [__smtx_typeof_value, hm] at h
  | Seq ss =>
      rcases typeof_seq_value_shape ss with ⟨A, hs⟩ | hs <;>
        simp [__smtx_typeof_value, hs] at h
  | Char c =>
      by_cases hc : native_char_valid c = true <;>
        simp [__smtx_typeof_value, native_ite, hc] at h
  | DtCons s' dd' j =>
      exfalso
      rcases dt_cons_result_chain s' dd' j (SmtType.BitVec w) h
          (by intro hEq; cases hEq) with ⟨Us, hChain⟩
      exact not_chain_of_base hChain.symm
        (by intro _ _ hEq; cases hEq) (by intro _ _ hEq; cases hEq)
  | Apply f a =>
      exfalso
      rcases apply_result_chain f a (SmtType.BitVec w) h
          (by intro hEq; cases hEq) with ⟨s, dd, Us, hChain⟩
      exact not_chain_of_base hChain.symm
        (by intro _ _ hEq; cases hEq) (by intro _ _ hEq; cases hEq)
  | _ => simp [__smtx_typeof_value] at h

private theorem typed_char_shape (v : SmtValue)
    (h : __smtx_typeof_value v = SmtType.Char) :
    ∃ c : native_Char, v = SmtValue.Char c := by
  cases v with
  | Char c => exact ⟨c, rfl⟩
  | Binary wi n =>
      by_cases hc :
          (native_and (native_zleq 0 wi)
            (native_zeq n (native_mod_total n (native_int_pow2 wi)))) = true <;>
        simp [__smtx_typeof_value, native_ite, hc] at h
  | Map m =>
      rcases typeof_map_value_shape m with ⟨A, B, hm⟩ | hm <;>
        simp [__smtx_typeof_value, hm] at h
  | Set m =>
      rcases map_to_set_type_shape (__smtx_typeof_map_value m) with
        ⟨A, hm⟩ | hm <;>
        simp [__smtx_typeof_value, hm] at h
  | Seq ss =>
      rcases typeof_seq_value_shape ss with ⟨A, hs⟩ | hs <;>
        simp [__smtx_typeof_value, hs] at h
  | DtCons s' dd' j =>
      exfalso
      rcases dt_cons_result_chain s' dd' j SmtType.Char h
          (by intro hEq; cases hEq) with ⟨Us, hChain⟩
      exact not_chain_of_base hChain.symm
        (by intro _ _ hEq; cases hEq) (by intro _ _ hEq; cases hEq)
  | Apply f a =>
      exfalso
      rcases apply_result_chain f a SmtType.Char h
          (by intro hEq; cases hEq) with ⟨s, dd, Us, hChain⟩
      exact not_chain_of_base hChain.symm
        (by intro _ _ hEq; cases hEq) (by intro _ _ hEq; cases hEq)
  | _ => simp [__smtx_typeof_value] at h

private theorem typed_map_shape (v : SmtValue) (T U : SmtType)
    (h : __smtx_typeof_value v = SmtType.Map T U) :
    ∃ m : SmtMap, v = SmtValue.Map m := by
  cases v with
  | Map m => exact ⟨m, rfl⟩
  | Binary wi n =>
      by_cases hc :
          (native_and (native_zleq 0 wi)
            (native_zeq n (native_mod_total n (native_int_pow2 wi)))) = true <;>
        simp [__smtx_typeof_value, native_ite, hc] at h
  | Set m =>
      rcases map_to_set_type_shape (__smtx_typeof_map_value m) with
        ⟨A, hm⟩ | hm <;>
        simp [__smtx_typeof_value, hm] at h
  | Seq ss =>
      rcases typeof_seq_value_shape ss with ⟨A, hs⟩ | hs <;>
        simp [__smtx_typeof_value, hs] at h
  | Char c =>
      by_cases hc : native_char_valid c = true <;>
        simp [__smtx_typeof_value, native_ite, hc] at h
  | DtCons s' dd' j =>
      exfalso
      rcases dt_cons_result_chain s' dd' j (SmtType.Map T U) h
          (by intro hEq; cases hEq) with ⟨Us, hChain⟩
      exact not_chain_of_base hChain.symm
        (by intro _ _ hEq; cases hEq) (by intro _ _ hEq; cases hEq)
  | Apply f a =>
      exfalso
      rcases apply_result_chain f a (SmtType.Map T U) h
          (by intro hEq; cases hEq) with ⟨s, dd, Us, hChain⟩
      exact not_chain_of_base hChain.symm
        (by intro _ _ hEq; cases hEq) (by intro _ _ hEq; cases hEq)
  | _ => simp [__smtx_typeof_value] at h

private theorem typed_set_shape (v : SmtValue) (T : SmtType)
    (h : __smtx_typeof_value v = SmtType.Set T) :
    ∃ m : SmtMap, v = SmtValue.Set m := by
  cases v with
  | Set m => exact ⟨m, rfl⟩
  | Binary wi n =>
      by_cases hc :
          (native_and (native_zleq 0 wi)
            (native_zeq n (native_mod_total n (native_int_pow2 wi)))) = true <;>
        simp [__smtx_typeof_value, native_ite, hc] at h
  | Map m =>
      rcases typeof_map_value_shape m with ⟨A, B, hm⟩ | hm <;>
        simp [__smtx_typeof_value, hm] at h
  | Seq ss =>
      rcases typeof_seq_value_shape ss with ⟨A, hs⟩ | hs <;>
        simp [__smtx_typeof_value, hs] at h
  | Char c =>
      by_cases hc : native_char_valid c = true <;>
        simp [__smtx_typeof_value, native_ite, hc] at h
  | DtCons s' dd' j =>
      exfalso
      rcases dt_cons_result_chain s' dd' j (SmtType.Set T) h
          (by intro hEq; cases hEq) with ⟨Us, hChain⟩
      exact not_chain_of_base hChain.symm
        (by intro _ _ hEq; cases hEq) (by intro _ _ hEq; cases hEq)
  | Apply f a =>
      exfalso
      rcases apply_result_chain f a (SmtType.Set T) h
          (by intro hEq; cases hEq) with ⟨s, dd, Us, hChain⟩
      exact not_chain_of_base hChain.symm
        (by intro _ _ hEq; cases hEq) (by intro _ _ hEq; cases hEq)
  | _ => simp [__smtx_typeof_value] at h

-- === constructor-spine inversion ===

private theorem build_spine_snoc :
    ∀ (vs : List SmtValue) (f a : SmtValue),
      build_spine f (vs ++ [a]) = SmtValue.Apply (build_spine f vs) a
  | [], f, a => by
      simp [build_spine]
  | v :: vs, f, a => by
      simpa [build_spine] using build_spine_snoc vs (SmtValue.Apply f v) a

private theorem list_typed_canonical_snoc
    {vs : List SmtValue} {Us : List SmtType}
    (h : list_typed_canonical vs Us)
    {a : SmtValue} {U : SmtType}
    (ha : __smtx_typeof_value a = U) (hU : U ≠ SmtType.None)
    (hc : __smtx_value_canonical a = true) :
    list_typed_canonical (vs ++ [a]) (Us ++ [U]) :=
  list_typed_canonical_append h ⟨⟨ha, hU, hc⟩, trivial⟩

/--
Constructor-spine inversion: every canonical value whose type is a
constructor chain over `Datatype s dd` is a partial constructor application
of one of the declared constructors, with typed canonical arguments for the
consumed fields.
-/
private theorem chain_typed_spine :
    ∀ (v : SmtValue) (s : native_String) (dd : SmtDatatypeDecl)
      (Us : List SmtType),
      __smtx_typeof_value v = dtc_chain_type (SmtType.Datatype s dd) Us ->
      __smtx_value_canonical v = true ->
      ∃ (k : Nat) (cr : SmtDatatypeCons) (consumed : List SmtType)
        (vs : List SmtValue),
        dt_nth_cons (__smtx_dt_resolve (__smtx_dd_lookup s dd) dd) k =
          some cr ∧
        dtc_fields cr = consumed ++ Us ∧
        v = build_spine (SmtValue.DtCons s dd k) vs ∧
        list_typed_canonical vs consumed
  | SmtValue.NotValue, s, dd, Us, h, _ => by
      exfalso
      exact not_chain_of_base (Eq.symm h)
        (by simp [__smtx_typeof_value]) (by simp [__smtx_typeof_value])
  | SmtValue.Boolean b, s, dd, Us, h, _ => by
      exfalso
      exact not_chain_of_base (Eq.symm h)
        (by simp [__smtx_typeof_value]) (by simp [__smtx_typeof_value])
  | SmtValue.Numeral n, s, dd, Us, h, _ => by
      exfalso
      exact not_chain_of_base (Eq.symm h)
        (by simp [__smtx_typeof_value]) (by simp [__smtx_typeof_value])
  | SmtValue.Rational q, s, dd, Us, h, _ => by
      exfalso
      exact not_chain_of_base (Eq.symm h)
        (by simp [__smtx_typeof_value]) (by simp [__smtx_typeof_value])
  | SmtValue.Binary w n, s, dd, Us, h, _ => by
      exfalso
      by_cases hc :
          (native_and (native_zleq 0 w)
            (native_zeq n (native_mod_total n (native_int_pow2 w)))) = true <;>
        exact not_chain_of_base (Eq.symm h)
          (by simp [__smtx_typeof_value, native_ite, hc])
          (by simp [__smtx_typeof_value, native_ite, hc])
  | SmtValue.Map m, s, dd, Us, h, _ => by
      exfalso
      rcases typeof_map_value_shape m with ⟨A, B, hm⟩ | hm <;>
        exact not_chain_of_base (Eq.symm h)
          (by simp [__smtx_typeof_value, hm])
          (by simp [__smtx_typeof_value, hm])
  | SmtValue.Fun i T1 U1, s, dd, Us, h, _ => by
      exfalso
      exact not_chain_of_base (Eq.symm h)
        (by simp [__smtx_typeof_value]) (by simp [__smtx_typeof_value])
  | SmtValue.Set m, s, dd, Us, h, _ => by
      exfalso
      rcases map_to_set_type_shape (__smtx_typeof_map_value m) with
        ⟨A, hm⟩ | hm <;>
        exact not_chain_of_base (Eq.symm h)
          (by simp [__smtx_typeof_value, hm])
          (by simp [__smtx_typeof_value, hm])
  | SmtValue.Seq ss, s, dd, Us, h, _ => by
      exfalso
      rcases typeof_seq_value_shape ss with ⟨A, hs⟩ | hs <;>
        exact not_chain_of_base (Eq.symm h)
          (by simp [__smtx_typeof_value, hs])
          (by simp [__smtx_typeof_value, hs])
  | SmtValue.Char c, s, dd, Us, h, _ => by
      exfalso
      by_cases hc : native_char_valid c = true <;>
        exact not_chain_of_base (Eq.symm h)
          (by simp [__smtx_typeof_value, native_ite, hc])
          (by simp [__smtx_typeof_value, native_ite, hc])
  | SmtValue.UValue i e, s, dd, Us, h, _ => by
      exfalso
      exact not_chain_of_base (Eq.symm h)
        (by simp [__smtx_typeof_value]) (by simp [__smtx_typeof_value])
  | SmtValue.RegLan r, s, dd, Us, h, _ => by
      exfalso
      exact not_chain_of_base (Eq.symm h)
        (by simp [__smtx_typeof_value]) (by simp [__smtx_typeof_value])
  | SmtValue.DtCons s' dd' j, s, dd, Us, h, _ => by
      have hTy :
          __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s' dd')
              (__smtx_dt_resolve (__smtx_dd_lookup s' dd') dd') j =
            dtc_chain_type (SmtType.Datatype s dd) Us := by
        simpa [__smtx_typeof_value] using h
      rcases dt_cons_value_rec_cases (SmtType.Datatype s' dd')
          (__smtx_dt_resolve (__smtx_dd_lookup s' dd') dd') j with
        hNone | ⟨cr, hnth, hChain⟩
      · rw [hNone] at hTy
        exact absurd hTy.symm (chain_ne_none s dd Us)
      · rw [hChain] at hTy
        rcases chain_inj s' dd' s dd (dtc_fields cr) Us hTy with
          ⟨hs, hdd, hFields⟩
        subst s'
        subst dd'
        exact ⟨j, cr, [], [], hnth, by simpa using hFields, by
          simp [build_spine], trivial⟩
  | SmtValue.Apply f a, s, dd, Us, h, hCan => by
      have hTy :
          __smtx_typeof_apply_value (__smtx_typeof_value f)
              (__smtx_typeof_value a) =
            dtc_chain_type (SmtType.Datatype s dd) Us := by
        simpa [__smtx_typeof_value] using h
      rcases apply_value_inversion hTy (chain_ne_none s dd Us) with
        ⟨hf, haN⟩
      have hCanParts :
          __smtx_value_canonical f = true ∧
            __smtx_value_canonical a = true := by
        simpa [__smtx_value_canonical, native_and] using hCan
      have hfChain :
          __smtx_typeof_value f =
            dtc_chain_type (SmtType.Datatype s dd)
              (__smtx_typeof_value a :: Us) := by
        rw [hf]
        rfl
      rcases chain_typed_spine f s dd (__smtx_typeof_value a :: Us)
          hfChain hCanParts.1 with
        ⟨k, cr, consumed, vs, hnth, hFields, hSpine, hTyped⟩
      refine ⟨k, cr, consumed ++ [__smtx_typeof_value a], vs ++ [a],
        hnth, ?_, ?_, ?_⟩
      · rw [hFields]
        simp
      · rw [hSpine, build_spine_snoc]
      · exact list_typed_canonical_snoc hTyped rfl haN hCanParts.2

/--
Top-level spine inversion: every typed canonical value of a datatype type is
a full application of a declared constructor to typed canonical arguments.
-/
theorem datatype_typed_canonical_spine
    (v : SmtValue) (s : native_String) (dd : SmtDatatypeDecl)
    (hTy : __smtx_typeof_value v = SmtType.Datatype s dd)
    (hCan : __smtx_value_canonical v = true) :
    ∃ (k : Nat) (cr : SmtDatatypeCons) (vs : List SmtValue),
      dt_nth_cons (__smtx_dt_resolve (__smtx_dd_lookup s dd) dd) k =
        some cr ∧
      v = build_spine (SmtValue.DtCons s dd k) vs ∧
      list_typed_canonical vs (dtc_fields cr) := by
  rcases chain_typed_spine v s dd [] (by simpa [dtc_chain_type] using hTy)
      hCan with ⟨k, cr, consumed, vs, hnth, hFields, hSpine, hTyped⟩
  refine ⟨k, cr, vs, hnth, hSpine, ?_⟩
  rw [hFields]
  simpa using hTyped


/-!
## Statement 3: unit soundness
-/

-- === map component extraction ===

private theorem map_value_cons_parts {i e : SmtValue} {m : SmtMap}
    {T U : SmtType}
    (h : __smtx_typeof_map_value (SmtMap.cons i e m) = SmtType.Map T U) :
    __smtx_typeof_value i = T ∧ __smtx_typeof_value e = U ∧
      __smtx_typeof_map_value m = SmtType.Map T U := by
  by_cases hc :
      (native_Teq
        (SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e))
        (__smtx_typeof_map_value m)) = true
  · have hm : __smtx_typeof_map_value m = SmtType.Map T U := by
      simpa [__smtx_typeof_map_value, native_ite, hc] using h
    have hEq :
        SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e) =
          SmtType.Map T U := by
      have := (by simpa [native_Teq] using hc :
        SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e) =
          __smtx_typeof_map_value m)
      rw [this, hm]
    injection hEq with h1 h2
    exact ⟨h1, h2, hm⟩
  · simp [__smtx_typeof_map_value, native_ite, hc] at h

private theorem map_value_default_parts {T' : SmtType} {e : SmtValue}
    {T U : SmtType}
    (h : __smtx_typeof_map_value (SmtMap.default T' e) = SmtType.Map T U) :
    T' = T ∧ __smtx_typeof_value e = U := by
  have h' :
      SmtType.Map T' (__smtx_typeof_value e) = SmtType.Map T U := by
    simpa [__smtx_typeof_map_value] using h
  injection h' with h1 h2
  exact ⟨h1, h2⟩

private theorem map_canonical_cons_parts {i e : SmtValue} {m : SmtMap}
    (h : __smtx_map_canonical (SmtMap.cons i e m) = true) :
    __smtx_value_canonical i = true ∧
      __smtx_value_canonical e = true ∧
      __smtx_map_canonical m = true ∧
      native_veq e (__smtx_map_get_default m) = false := by
  simp only [__smtx_map_canonical, native_and, native_not,
    Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.2⟩

private theorem map_canonical_default_parts {T : SmtType} {e : SmtValue}
    (h : __smtx_map_canonical (SmtMap.default T e) = true) :
    __smtx_value_canonical e = true := by
  simp only [__smtx_map_canonical, native_and, Bool.and_eq_true] at h
  exact h.2

private theorem get_default_typed :
    ∀ (m : SmtMap) (T U : SmtType),
      __smtx_typeof_map_value m = SmtType.Map T U ->
        __smtx_typeof_value (__smtx_map_get_default m) = U
  | SmtMap.default T' e, T, U, h => by
      rcases map_value_default_parts h with ⟨_, he⟩
      simpa [__smtx_map_get_default] using he
  | SmtMap.cons i e m, T, U, h => by
      rcases map_value_cons_parts h with ⟨_, _, hm⟩
      simpa [__smtx_map_get_default] using get_default_typed m T U hm

private theorem get_default_canonical :
    ∀ m : SmtMap,
      __smtx_map_canonical m = true ->
        __smtx_value_canonical (__smtx_map_get_default m) = true
  | SmtMap.default T e, h => by
      simpa [__smtx_map_get_default] using map_canonical_default_parts h
  | SmtMap.cons i e m, h => by
      rcases map_canonical_cons_parts h with ⟨_, _, hm, _⟩
      simpa [__smtx_map_get_default] using get_default_canonical m hm

-- === unit fixpoint body shape ===

private theorem unit_body_shape {d : SmtDatatype} {B : SmtDatatypeDecl}
    (h : __smtx_datatype_bounded true d B = true) :
    ∃ c : SmtDatatypeCons,
      d = SmtDatatype.sum c SmtDatatype.null ∧
        __smtx_datatype_cons_bounded true c B = true := by
  cases d with
  | null =>
      simp [__smtx_datatype_bounded, native_not] at h
  | sum c dRest =>
      cases dRest with
      | null =>
          exact ⟨c, rfl, by simpa [__smtx_datatype_bounded] using h⟩
      | sum c2 d2 =>
          simp [__smtx_datatype_bounded, native_and, native_not] at h

-- === all-default argument lists ===

private theorem list_typed_all_default :
    ∀ (Us : List SmtType) (vs : List SmtValue),
      list_typed_canonical vs Us ->
      (∀ U ∈ Us, ∀ w : SmtValue,
        __smtx_typeof_value w = U ->
        __smtx_value_canonical w = true ->
        w = __smtx_type_default U) ->
      vs = defaults_of Us
  | [], [], _, _ => rfl
  | [], v :: vs, h, _ => by
      simp [list_typed_canonical] at h
  | U :: Us, [], h, _ => by
      simp [list_typed_canonical] at h
  | U :: Us, v :: vs, h, hUniq => by
      have hParts := h
      simp only [list_typed_canonical] at hParts
      have hHead : v = __smtx_type_default U :=
        hUniq U (by simp) v hParts.1.1 hParts.1.2.2
      have hTail : vs = defaults_of Us :=
        list_typed_all_default Us vs hParts.2
          (fun U' hU' => hUniq U' (by simp [hU']))
      rw [defaults_of, hHead, hTail]

-- === the generated default of a single-constructor datatype, as a spine ===

private theorem restricted_slots_eq_defaults
    (dd ddTail : SmtDatatypeDecl)
    (hUniq : dd_unique dd)
    (hSufTail : SuffixOf ddTail dd) :
    ∀ Ts : List SmtType,
      (∀ w ∈ restricted_slots dd ddTail Ts, w ≠ SmtValue.NotValue) ->
      restricted_slots dd ddTail Ts =
        defaults_of (Ts.map (resolve_ty dd))
  | [], _ => rfl
  | T :: Ts, hNe => by
      have hHead :
          __smtx_field_type_default dd T ddTail =
            __smtx_type_default (resolve_ty dd T) := by
        by_cases hRef : ∃ t : native_String, T = SmtType.TypeRef t
        · rcases hRef with ⟨t, rfl⟩
          have hSlotNe :
              __smtx_datatype_decl_default t dd ddTail ≠
                SmtValue.NotValue := by
            have := hNe (__smtx_field_type_default dd (SmtType.TypeRef t) ddTail)
              (by simp [restricted_slots])
            rwa [field_type_default_ref] at this
          have hMemTail :=
            decl_default_has_dt_of_ne_notValue t dd ddTail hSlotNe
          rw [field_type_default_ref,
            suffix_decl_default_eq t dd hSufTail hUniq hMemTail]
          simp [resolve_ty, __smtx_type_default]
        · have hRef' : ∀ t : native_String, T ≠ SmtType.TypeRef t := by
            intro t ht
            exact hRef ⟨t, ht⟩
          rw [field_type_default_ground dd ddTail T hRef',
            resolve_ty_ground dd T hRef']
      have hTail :=
        restricted_slots_eq_defaults dd ddTail hUniq hSufTail Ts
          (fun w hw => hNe w (by simp [restricted_slots, hw]))
      simp [restricted_slots, defaults_of, hHead, hTail]

private theorem unit_default_spine
    (s : native_String) (dd : SmtDatatypeDecl) (c : SmtDatatypeCons)
    (hInh : native_inhabited_type (SmtType.Datatype s dd) = true)
    (hMem : __smtx_dd_has_dt s dd = true)
    (hUniq : dd_unique dd)
    (hd : __smtx_dd_lookup s dd = SmtDatatype.sum c SmtDatatype.null) :
    __smtx_type_default (SmtType.Datatype s dd) =
      build_spine (SmtValue.DtCons s dd 0)
        (defaults_of ((dtc_fields c).map (resolve_ty dd))) := by
  rcases decl_default_find s dd dd hMem with ⟨ddTail, hSuf, hDefEq⟩
  have hDefaultRaw :
      __smtx_type_default (SmtType.Datatype s dd) =
        __smtx_datatype_decl_default s dd dd := by
    simp [__smtx_type_default]
  have hDefNe :
      __smtx_type_default (SmtType.Datatype s dd) ≠ SmtValue.NotValue :=
    default_ne_notValue_of_inh hInh
  have hSufTail : SuffixOf ddTail dd := by
    rw [hd] at hSuf
    exact suffixOf_cons_inner hSuf
  have hDefaultR :
      __smtx_type_default (SmtType.Datatype s dd) =
        __smtx_datatype_cons_default (SmtValue.DtCons s dd 0) dd c ddTail := by
    rw [hDefaultRaw, hDefEq, hd]
    cases hr :
        native_veq
          (__smtx_datatype_cons_default (SmtValue.DtCons s dd 0) dd c ddTail)
          SmtValue.NotValue with
    | false =>
        simp [__smtx_datatype_default, native_ite, native_not, hr]
    | true =>
        exfalso
        apply hDefNe
        rw [hDefaultRaw, hDefEq, hd]
        have hrEq := veq_eq_of_true hr
        simp [__smtx_datatype_default, native_ite, native_not, hr, hrEq]
  have hRNe :
      __smtx_datatype_cons_default (SmtValue.DtCons s dd 0) dd c ddTail ≠
        SmtValue.NotValue := by
    rw [← hDefaultR]
    exact hDefNe
  rcases cons_default_spine dd ddTail c (SmtValue.DtCons s dd 0) hRNe with
    ⟨hSpineEq, hSlotsNe⟩
  rw [hDefaultR, hSpineEq,
    restricted_slots_eq_defaults dd ddTail hUniq hSufTail (dtc_fields c)
      hSlotsNe]

/--
**Unit soundness** (statement 3): every typed canonical value of a
well-formed inhabited unit type is its default value.
-/
theorem unit_type_values_default
    (A : SmtType)
    (hInh : native_inhabited_type A = true)
    (hRec : __smtx_type_wf_rec A = true)
    (hUnit : __smtx_is_unit_type A = true) :
    ∀ v : SmtValue,
      __smtx_typeof_value v = A ->
      __smtx_value_canonical v = true ->
      v = __smtx_type_default A := by
  cases A with
  | None =>
      simp [__smtx_type_wf_rec] at hRec
  | RegLan =>
      simp [__smtx_type_wf_rec] at hRec
  | TypeRef t =>
      simp [__smtx_type_wf_rec] at hRec
  | FunType T U =>
      simp [__smtx_type_wf_rec] at hRec
  | DtcAppType T U =>
      simp [__smtx_type_wf_rec] at hRec
  | Bool =>
      simp [__smtx_is_unit_type, __smtx_type_bounded, native_not] at hUnit
  | Int =>
      simp [__smtx_is_unit_type, __smtx_type_bounded] at hUnit
  | Real =>
      simp [__smtx_is_unit_type, __smtx_type_bounded] at hUnit
  | Char =>
      simp [__smtx_is_unit_type, __smtx_type_bounded, native_not] at hUnit
  | Seq T =>
      simp [__smtx_is_unit_type, __smtx_type_bounded] at hUnit
  | Set T =>
      simp [__smtx_is_unit_type, __smtx_type_bounded, native_and,
        native_not] at hUnit
  | USort u =>
      simp [__smtx_is_unit_type, __smtx_type_bounded] at hUnit
  | BitVec w =>
      cases w with
      | succ w =>
          simp [__smtx_is_unit_type, __smtx_type_bounded, native_or,
            native_not, native_nateq] at hUnit
      | zero =>
          intro v hTy hCan
          rcases typed_bitvec_shape v 0 hTy with ⟨wi, n, rfl⟩
          by_cases hc :
              (native_and (native_zleq 0 wi)
                (native_zeq n (native_mod_total n (native_int_pow2 wi)))) =
                true
          · have hBV :
                SmtType.BitVec (native_int_to_nat wi) = SmtType.BitVec 0 := by
              simpa [__smtx_typeof_value, native_ite, hc] using hTy
            injection hBV with hw0
            have hParts :
                native_zleq 0 wi = true ∧
                  native_zeq n
                    (native_mod_total n (native_int_pow2 wi)) = true := by
              simpa [native_and] using hc
            have hwiNonneg : (0 : Int) ≤ wi := by
              simpa [native_zleq] using hParts.1
            have hwiToNat : Int.toNat wi = 0 := by
              simpa [native_int_to_nat] using hw0
            have hwiLe : wi ≤ 0 := Int.toNat_eq_zero.mp hwiToNat
            have hwi : wi = 0 := Int.le_antisymm hwiLe hwiNonneg
            subst wi
            have hPow : native_int_pow2 (0 : Int) = 1 := by
              simp [native_int_pow2, native_zexp_total]
            have hn : n = 0 := by
              have := hParts.2
              rw [hPow] at this
              simpa [native_zeq, native_mod_total, Int.emod_one] using this
            subst n
            simp [__smtx_type_default, native_nat_to_int]
          · simp [__smtx_typeof_value, native_ite, hc] at hTy
  | Map T U =>
      have hRecParts :
          native_inhabited_type T = true ∧
            __smtx_type_wf_rec T = true ∧
              native_inhabited_type U = true ∧
                __smtx_type_wf_rec U = true := by
        have h := hRec
        simp [__smtx_type_wf_rec, native_and] at h
        exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩
      have hUUnit : __smtx_is_unit_type U = true := by
        simpa [__smtx_is_unit_type, __smtx_type_bounded, native_or,
          native_and, native_not] using hUnit
      have hUNV : __smtx_type_default U ≠ SmtValue.NotValue :=
        default_ne_notValue_of_inh hRecParts.2.2.1
      intro v hTy hCan
      rcases typed_map_shape v T U hTy with ⟨m, rfl⟩
      have hmTy : __smtx_typeof_map_value m = SmtType.Map T U := by
        simpa [__smtx_typeof_value] using hTy
      have hmCan : __smtx_map_canonical m = true := by
        simpa [__smtx_value_canonical] using hCan
      cases m with
      | cons i e m' =>
          exfalso
          rcases map_value_cons_parts hmTy with ⟨hiT, heU, hm'Ty⟩
          rcases map_canonical_cons_parts hmCan with
            ⟨hiCan, heCan, hm'Can, heNe⟩
          have heDef : e = __smtx_type_default U :=
            unit_type_values_default U hRecParts.2.2.1 hRecParts.2.2.2
              hUUnit e heU heCan
          have hgTy : __smtx_typeof_value (__smtx_map_get_default m') = U :=
            get_default_typed m' T U hm'Ty
          have hgCan :
              __smtx_value_canonical (__smtx_map_get_default m') =
                true :=
            get_default_canonical m' hm'Can
          have hgDef : __smtx_map_get_default m' = __smtx_type_default U :=
            unit_type_values_default U hRecParts.2.2.1 hRecParts.2.2.2
              hUUnit _ hgTy hgCan
          rw [heDef, hgDef, veq_refl_true] at heNe
          cases heNe
      | default T' e0 =>
          rcases map_value_default_parts hmTy with ⟨hT', he0U⟩
          subst T'
          have he0Can := map_canonical_default_parts hmCan
          have he0 : e0 = __smtx_type_default U :=
            unit_type_values_default U hRecParts.2.2.1 hRecParts.2.2.2
              hUUnit e0 he0U he0Can
          subst e0
          rw [show __smtx_type_default (SmtType.Map T U) =
              native_ite
                (native_veq (__smtx_type_default U) SmtValue.NotValue)
                SmtValue.NotValue
                (SmtValue.Map (SmtMap.default T (__smtx_type_default U)))
              from by simp [__smtx_type_default]]
          simp [native_ite, native_veq, hUNV]
  | Datatype s dd =>
      have hRecParts :
          __smtx_dd_has_dt s dd = true ∧ __smtx_decl_wf_rec dd dd = true := by
        simpa [__smtx_type_wf_rec, native_and] using hRec
      have hUniq : dd_unique dd := dd_unique_of_decl_wf dd dd hRecParts.2
      have hFixMem :
          __smtx_dd_has_dt s
            (__smtx_datatype_decl_bounded true dd dd SmtDatatypeDecl.nil) =
            true := by
        rw [is_unit_datatype_eq] at hUnit
        exact hUnit
      intro v hTy hCan
      refine decl_bounded_payload true dd hUniq
        (fun t => ∀ w : SmtValue,
          __smtx_typeof_value w = SmtType.Datatype t dd ->
          __smtx_value_canonical w = true ->
          w = __smtx_type_default (SmtType.Datatype t dd))
        ?_ s hFixMem v hTy hCan
      intro t hMemDD B0 hBnd hInvB w hwTy hwCan
      rcases unit_body_shape hBnd with ⟨c, hdLk, hConsBnd⟩
      have hDtWf : __smtx_dt_wf_rec dd (__smtx_dd_lookup t dd) = true :=
        decl_wf_rec_lookup_local t dd dd hMemDD hRecParts.2
      have hConsWf : __smtx_dt_cons_wf_rec dd c = true := by
        rw [hdLk] at hDtWf
        simpa [__smtx_dt_wf_rec, native_and] using hDtWf
      have hInhT : native_inhabited_type (SmtType.Datatype t dd) = true :=
        decl_wf_rec_inh t dd dd hMemDD hRecParts.2
      rcases datatype_typed_canonical_spine w t dd hwTy hwCan with
        ⟨k, cr, vs, hnth, hSpine, hTyped⟩
      have hk : k = 0 ∧ cr = __smtx_dtc_resolve c dd := by
        rw [hdLk] at hnth
        cases k with
        | zero =>
            refine ⟨rfl, ?_⟩
            have : some (__smtx_dtc_resolve c dd) = some cr := by
              simpa [__smtx_dt_resolve, dt_nth_cons] using hnth
            injection this with h'
            exact h'.symm
        | succ k' =>
            simp [__smtx_dt_resolve, dt_nth_cons] at hnth
      rcases hk with ⟨hk0, hcr⟩
      subst hk0
      subst hcr
      have hFieldsEq :
          dtc_fields (__smtx_dtc_resolve c dd) =
            (dtc_fields c).map (resolve_ty dd) := dtc_resolve_fields dd c
      have hAllDefault :
          ∀ U ∈ (dtc_fields c).map (resolve_ty dd), ∀ w2 : SmtValue,
            __smtx_typeof_value w2 = U ->
            __smtx_value_canonical w2 = true ->
            w2 = __smtx_type_default U := by
        intro U hU w2 hw2Ty hw2Can
        rcases List.mem_map.mp hU with ⟨F, hFmem, hFeq⟩
        have hFieldBnd :
            __smtx_field_type_bounded true F B0 = true :=
          bounded_cons_field c hConsBnd F hFmem
        by_cases hRef : ∃ r : native_String, F = SmtType.TypeRef r
        · rcases hRef with ⟨r, rfl⟩
          have hrMem : __smtx_dd_has_dt r B0 = true := by
            simpa [__smtx_field_type_bounded] using hFieldBnd
          have hUEq : U = SmtType.Datatype r dd := by
            rw [← hFeq]
            simp [resolve_ty]
          rw [hUEq] at hw2Ty ⊢
          exact hInvB r hrMem w2 hw2Ty hw2Can
        · have hRef' : ∀ r : native_String, F ≠ SmtType.TypeRef r := by
            intro r hr
            exact hRef ⟨r, hr⟩
          have hUEq : U = F := by
            rw [← hFeq]
            exact resolve_ty_ground dd F hRef'
          rw [hUEq] at hw2Ty ⊢
          have hFUnit : __smtx_is_unit_type F = true := by
            have hBnd : __smtx_type_bounded true F = true := by
              cases F <;> first
                | exact absurd rfl (hRef' _)
                | simpa [__smtx_field_type_bounded] using hFieldBnd
            simpa [__smtx_is_unit_type] using hBnd
          have hFWf := resolved_field_inh_wf dd hRecParts.2 c hConsWf F hFmem
          rw [resolve_ty_ground dd F hRef'] at hFWf
          have hMeasure : sizeOf F < sizeOf dd := by
            have h1 := sizeOf_field_lt c F hFmem
            have h2 : sizeOf (SmtDatatype.sum c SmtDatatype.null) <
                sizeOf dd := by
              have := sizeOf_lookup_lt t dd hMemDD
              rwa [hdLk] at this
            have h3 : sizeOf c <
                sizeOf (SmtDatatype.sum c SmtDatatype.null) := by
              rw [show sizeOf (SmtDatatype.sum c SmtDatatype.null) =
                1 + sizeOf c + sizeOf SmtDatatype.null by rfl]
              omega
            omega
          exact unit_type_values_default F hFWf.1 hFWf.2 hFUnit w2
            hw2Ty hw2Can
      have hvsEq : vs = defaults_of ((dtc_fields c).map (resolve_ty dd)) := by
        refine list_typed_all_default _ vs ?_ hAllDefault
        rw [← hFieldsEq]
        exact hTyped
      rw [hSpine, hvsEq,
        ← unit_default_spine t dd c hInhT hMemDD hUniq hdLk]
termination_by sizeOf A
decreasing_by
  all_goals subst A
  all_goals first
    | (rw [show sizeOf (SmtType.Map T U) = 1 + sizeOf T + sizeOf U by rfl]
       omega)
    | (rw [show sizeOf (SmtType.Datatype s dd) =
          1 + sizeOf s + sizeOf dd by rfl]
       omega)


/-!
## Statement 1: finite soundness
-/

-- === list combinatorics ===

private theorem veq_false_ne {a b : SmtValue}
    (h : native_veq a b = false) : a ≠ b := by
  intro hEq
  subst hEq
  rw [veq_refl_true] at h
  cases h

/-- Pigeonhole: a duplicate-free list included in another is no longer. -/
private theorem nodup_subset_length :
    ∀ (l l' : List SmtValue), l.Nodup → l ⊆ l' → l.length ≤ l'.length
  | [], l', _, _ => Nat.zero_le _
  | a :: l, l', hNodup, hSub => by
      have hMem : a ∈ l' := hSub (by simp)
      have hParts := List.nodup_cons.mp hNodup
      have hSub' : l ⊆ l'.erase a := by
        intro x hx
        have hxl' : x ∈ l' := hSub (by simp [hx])
        have hxa : x ≠ a := by
          intro hEq
          subst hEq
          exact hParts.1 hx
        exact (List.mem_erase_of_ne hxa).mpr hxl'
      have hRec := nodup_subset_length l (l'.erase a) hParts.2 hSub'
      have hLen : (l'.erase a).length = l'.length - 1 :=
        List.length_erase_of_mem hMem
      have hPos : 0 < l'.length := List.length_pos_of_mem hMem
      simp only [List.length_cons]
      omega

/-- All lists of length at most `n` over a given alphabet. -/
private def lists_up_to (alphabet : List SmtValue) : Nat → List (List SmtValue)
  | 0 => [[]]
  | Nat.succ n =>
      [] :: alphabet.flatMap (fun a => (lists_up_to alphabet n).map (a :: ·))

private theorem lists_up_to_complete (alphabet : List SmtValue) :
    ∀ (n : Nat) (l : List SmtValue),
      (∀ x ∈ l, x ∈ alphabet) → l.length ≤ n → l ∈ lists_up_to alphabet n
  | n, [], _, _ => by
      cases n <;> simp [lists_up_to]
  | 0, a :: l, _, hLen => by
      simp at hLen
  | Nat.succ n, a :: l, hMem, hLen => by
      have hRec := lists_up_to_complete alphabet n l
        (fun x hx => hMem x (by simp [hx])) (by simpa using hLen)
      simp only [lists_up_to, List.mem_cons, List.mem_flatMap, List.mem_map]
      exact Or.inr ⟨a, hMem a (by simp), l, hRec, rfl⟩

/-- Value pairs drawn from two alphabets (used for map entries). -/
private def pairs_of (la lb : List SmtValue) : List SmtValue :=
  la.flatMap (fun a => lb.map (fun b => SmtValue.Apply a b))

-- We reuse `SmtValue.Apply` as an anonymous pairing constructor for the
-- entry alphabet; only membership matters, never typing.

private theorem pairs_of_mem {la lb : List SmtValue} {a b : SmtValue}
    (ha : a ∈ la) (hb : b ∈ lb) : SmtValue.Apply a b ∈ pairs_of la lb := by
  simp only [pairs_of, List.mem_flatMap, List.mem_map]
  exact ⟨a, ha, b, hb, rfl⟩

-- === map entry lists ===

private def map_entries : SmtMap → List (SmtValue × SmtValue)
  | SmtMap.cons i e m => (i, e) :: map_entries m
  | SmtMap.default _ _ => []

private def mk_map (T : SmtType) (d : SmtValue) :
    List (SmtValue × SmtValue) → SmtMap
  | [] => SmtMap.default T d
  | (i, e) :: ps => SmtMap.cons i e (mk_map T d ps)

private theorem map_rebuild :
    ∀ (m : SmtMap) (T U : SmtType),
      __smtx_typeof_map_value m = SmtType.Map T U →
        m = mk_map T (__smtx_map_get_default m) (map_entries m)
  | SmtMap.default T' e, T, U, h => by
      rcases map_value_default_parts h with ⟨hT', _⟩
      subst hT'
      simp [map_entries, mk_map, __smtx_map_get_default]
  | SmtMap.cons i e m, T, U, h => by
      rcases map_value_cons_parts h with ⟨_, _, hm⟩
      have hRec := map_rebuild m T U hm
      simp only [map_entries, mk_map, __smtx_map_get_default]
      exact congrArg (SmtMap.cons i e) hRec

private theorem map_entries_typed :
    ∀ (m : SmtMap) (T U : SmtType),
      __smtx_typeof_map_value m = SmtType.Map T U →
        ∀ p ∈ map_entries m,
          __smtx_typeof_value p.1 = T ∧ __smtx_typeof_value p.2 = U
  | SmtMap.default T' e, T, U, _, p, hp => by
      simp [map_entries] at hp
  | SmtMap.cons i e m, T, U, h, p, hp => by
      rcases map_value_cons_parts h with ⟨hi, he, hm⟩
      rcases List.mem_cons.mp hp with hEq | hTail
      · subst hEq
        exact ⟨hi, he⟩
      · exact map_entries_typed m T U hm p hTail

private theorem map_entries_canonical :
    ∀ m : SmtMap,
      __smtx_map_canonical m = true →
        ∀ p ∈ map_entries m,
          __smtx_value_canonical p.1 = true ∧
            __smtx_value_canonical p.2 = true
  | SmtMap.default T' e, _, p, hp => by
      simp [map_entries] at hp
  | SmtMap.cons i e m, h, p, hp => by
      rcases map_canonical_cons_parts h with ⟨hi, he, hm, _⟩
      rcases List.mem_cons.mp hp with hEq | hTail
      · subst hEq
        exact ⟨hi, he⟩
      · exact map_entries_canonical m hm p hTail

private theorem map_canonical_cons_ordered {i e : SmtValue} {m : SmtMap}
    (h : __smtx_map_canonical (SmtMap.cons i e m) = true) :
    __smtx_map_entries_ordered_after i m = true := by
  simp only [__smtx_map_canonical, native_and, Bool.and_eq_true] at h
  exact h.1.2

private theorem map_keys_below :
    ∀ (m : SmtMap) (i : SmtValue),
      __smtx_map_canonical m = true →
      __smtx_map_entries_ordered_after i m = true →
      ∀ p ∈ map_entries m, native_vcmp p.1 i = true
  | SmtMap.default T e, i, _, _, p, hp => by
      simp [map_entries] at hp
  | SmtMap.cons j e m, i, hCan, hOrd, p, hp => by
      have hji : native_vcmp j i = true := by
        simpa [__smtx_map_entries_ordered_after] using hOrd
      rcases map_canonical_cons_parts hCan with ⟨_, _, hmCan, _⟩
      have hOrd' : __smtx_map_entries_ordered_after j m = true :=
        map_canonical_cons_ordered hCan
      rcases List.mem_cons.mp hp with hEq | hTail
      · subst hEq
        exact hji
      · have := map_keys_below m j hmCan hOrd' p hTail
        exact native_vcmp_trans this hji

private theorem map_keys_nodup :
    ∀ m : SmtMap,
      __smtx_map_canonical m = true →
        ((map_entries m).map Prod.fst).Nodup
  | SmtMap.default T e, _ => by
      simp [map_entries]
  | SmtMap.cons i e m, h => by
      rcases map_canonical_cons_parts h with ⟨_, _, hmCan, _⟩
      have hOrd : __smtx_map_entries_ordered_after i m = true :=
        map_canonical_cons_ordered h
      simp only [map_entries, List.map_cons]
      refine List.nodup_cons.mpr ⟨?_, map_keys_nodup m hmCan⟩
      intro hMem
      rcases List.mem_map.mp hMem with ⟨p, hp, hpi⟩
      have hCmp := map_keys_below m i hmCan hOrd p hp
      rw [hpi] at hCmp
      have hNe := native_vcmp_ne hCmp
      rw [veq_refl_true] at hNe
      cases hNe

private theorem map_default_forced :
    ∀ (m : SmtMap) (T U : SmtType),
      __smtx_is_finite_type T = true →
      __smtx_typeof_map_value m = SmtType.Map T U →
      __smtx_map_canonical m = true →
        __smtx_map_get_default m = __smtx_type_default U
  | SmtMap.default T' e, T, U, hFin, hTy, hCan => by
      rcases map_value_default_parts hTy with ⟨hT', he⟩
      subst hT'
      have hDef : __smtx_map_default_canonical T' e = true := by
        simp only [__smtx_map_canonical, native_and, Bool.and_eq_true] at hCan
        exact hCan.1
      rw [__smtx_map_default_canonical, native_ite, if_pos hFin] at hDef
      have := veq_eq_of_true hDef
      rw [he] at this
      simpa [__smtx_map_get_default] using this
  | SmtMap.cons i e m, T, U, hFin, hTy, hCan => by
      rcases map_value_cons_parts hTy with ⟨_, _, hm⟩
      rcases map_canonical_cons_parts hCan with ⟨_, _, hmCan, _⟩
      simpa [__smtx_map_get_default] using
        map_default_forced m T U hFin hm hmCan

private theorem map_to_set_type_inv {X T : SmtType}
    (h : __smtx_map_to_set_type X = SmtType.Set T) :
    X = SmtType.Map T SmtType.Bool := by
  cases X
  case Map A B =>
    cases B
    case Bool =>
      have hAT : A = T := by
        simpa [__smtx_map_to_set_type] using h
      rw [hAT]
    all_goals simp [__smtx_map_to_set_type] at h
  all_goals simp [__smtx_map_to_set_type] at h

-- === map and set covers ===

private def entry_pack : SmtValue × SmtValue → SmtValue
  | (i, e) => SmtValue.Apply i e

private def entry_unpack_list : List SmtValue → List (SmtValue × SmtValue)
  | [] => []
  | SmtValue.Apply i e :: rest => (i, e) :: entry_unpack_list rest
  | _ :: rest => entry_unpack_list rest

private theorem entry_unpack_pack :
    ∀ ps : List (SmtValue × SmtValue),
      entry_unpack_list (ps.map entry_pack) = ps
  | [] => rfl
  | (i, e) :: ps => by
      simp [entry_pack, entry_unpack_list, entry_unpack_pack ps]

/-- Cover for canonical maps with finite domain and range covers. -/
private theorem map_cover_exists
    (T U : SmtType) (lT lU : List SmtValue)
    (hFinT : __smtx_is_finite_type T = true)
    (hlT : ∀ v : SmtValue, __smtx_typeof_value v = T →
      __smtx_value_canonical v = true → v ∈ lT)
    (hlU : ∀ v : SmtValue, __smtx_typeof_value v = U →
      __smtx_value_canonical v = true → v ∈ lU) :
    ∃ l : List SmtValue, ∀ v : SmtValue,
      __smtx_typeof_value v = SmtType.Map T U →
      __smtx_value_canonical v = true → v ∈ l := by
  refine ⟨(lists_up_to (pairs_of lT lU) lT.length).map
    (fun ps => SmtValue.Map
      (mk_map T (__smtx_type_default U) (entry_unpack_list ps))), ?_⟩
  intro v hTy hCan
  rcases typed_map_shape v T U hTy with ⟨m, rfl⟩
  have hmTy : __smtx_typeof_map_value m = SmtType.Map T U := by
    simpa [__smtx_typeof_value] using hTy
  have hmCan : __smtx_map_canonical m = true := by
    simpa [__smtx_value_canonical] using hCan
  have hDefault : __smtx_map_get_default m = __smtx_type_default U :=
    map_default_forced m T U hFinT hmTy hmCan
  have hRebuild := map_rebuild m T U hmTy
  have hPacked :
      (map_entries m).map entry_pack ∈
        lists_up_to (pairs_of lT lU) lT.length := by
    refine lists_up_to_complete (pairs_of lT lU) lT.length _ ?_ ?_
    · intro x hx
      rcases List.mem_map.mp hx with ⟨p, hp, hpx⟩
      have hTyped := map_entries_typed m T U hmTy p hp
      have hCanP := map_entries_canonical m hmCan p hp
      have hi : p.1 ∈ lT := hlT p.1 hTyped.1 hCanP.1
      have he : p.2 ∈ lU := hlU p.2 hTyped.2 hCanP.2
      rw [← hpx]
      cases p with
      | mk i e => exact pairs_of_mem hi he
    · have hNodup := map_keys_nodup m hmCan
      have hSub : (map_entries m).map Prod.fst ⊆ lT := by
        intro x hx
        rcases List.mem_map.mp hx with ⟨p, hp, hpx⟩
        have hTyped := map_entries_typed m T U hmTy p hp
        have hCanP := map_entries_canonical m hmCan p hp
        rw [← hpx]
        exact hlT p.1 hTyped.1 hCanP.1
      have := nodup_subset_length _ lT hNodup hSub
      simpa using this
  refine List.mem_map.mpr ⟨(map_entries m).map entry_pack, hPacked, ?_⟩
  rw [entry_unpack_pack, ← hDefault, ← hRebuild]

private theorem set_entries_true :
    ∀ (m : SmtMap) (T : SmtType),
      __smtx_typeof_map_value m = SmtType.Map T SmtType.Bool →
      __smtx_map_canonical m = true →
      __smtx_map_get_default m = SmtValue.Boolean false →
      ∀ p ∈ map_entries m, p.2 = SmtValue.Boolean true
  | SmtMap.default T' e, T, _, _, _, p, hp => by
      simp [map_entries] at hp
  | SmtMap.cons i e m, T, hTy, hCan, hDef, p, hp => by
      rcases map_value_cons_parts hTy with ⟨_, heBool, hmTy⟩
      rcases map_canonical_cons_parts hCan with ⟨_, heCan, hmCan, heNe⟩
      have hDef' : __smtx_map_get_default m = SmtValue.Boolean false := by
        simpa [__smtx_map_get_default] using hDef
      rcases List.mem_cons.mp hp with hEq | hTail
      · subst hEq
        rcases typed_bool_shape e heBool with ⟨b, hb⟩
        cases b with
        | true => simpa using hb
        | false =>
            exfalso
            rw [hb, hDef', veq_refl_true] at heNe
            cases heNe
      · exact set_entries_true m T hmTy hmCan hDef' p hTail

private theorem entries_eq_keys_map :
    ∀ ps : List (SmtValue × SmtValue),
      (∀ p ∈ ps, p.2 = SmtValue.Boolean true) →
        ps = (ps.map Prod.fst).map (fun k => (k, SmtValue.Boolean true))
  | [], _ => rfl
  | (i, e) :: ps, h => by
      have hHead : e = SmtValue.Boolean true := h (i, e) (by simp)
      have hTail := entries_eq_keys_map ps (fun p hp => h p (by simp [hp]))
      simp only [List.map_cons]
      rw [← hTail, hHead]

/-- Cover for canonical sets with a finite element cover. -/
private theorem set_cover_exists
    (T : SmtType) (lT : List SmtValue)
    (hlT : ∀ v : SmtValue, __smtx_typeof_value v = T →
      __smtx_value_canonical v = true → v ∈ lT) :
    ∃ l : List SmtValue, ∀ v : SmtValue,
      __smtx_typeof_value v = SmtType.Set T →
      __smtx_value_canonical v = true → v ∈ l := by
  refine ⟨(lists_up_to lT lT.length).map
    (fun ks => SmtValue.Set
      (mk_map T (SmtValue.Boolean false)
        (ks.map (fun k => (k, SmtValue.Boolean true))))), ?_⟩
  intro v hTy hCan
  rcases typed_set_shape v T hTy with ⟨m, rfl⟩
  have hmTy : __smtx_typeof_map_value m = SmtType.Map T SmtType.Bool := by
    have h' :
        __smtx_map_to_set_type (__smtx_typeof_map_value m) =
          SmtType.Set T := by
      simpa [__smtx_typeof_value] using hTy
    exact map_to_set_type_inv h'
  have hCanParts :
      __smtx_map_canonical m = true ∧
        native_veq (__smtx_map_get_default m) (SmtValue.Boolean false) =
          true := by
    simpa [__smtx_value_canonical, native_and] using hCan
  have hDefault : __smtx_map_get_default m = SmtValue.Boolean false :=
    veq_eq_of_true hCanParts.2
  have hValuesTrue :=
    set_entries_true m T hmTy hCanParts.1 hDefault
  have hKeysMem :
      ((map_entries m).map Prod.fst) ∈ lists_up_to lT lT.length := by
    refine lists_up_to_complete lT lT.length _ ?_ ?_
    · intro x hx
      rcases List.mem_map.mp hx with ⟨p, hp, hpx⟩
      have hTyped := map_entries_typed m T SmtType.Bool hmTy p hp
      have hCanP := map_entries_canonical m hCanParts.1 p hp
      rw [← hpx]
      exact hlT p.1 hTyped.1 hCanP.1
    · have hNodup := map_keys_nodup m hCanParts.1
      have hSub : (map_entries m).map Prod.fst ⊆ lT := by
        intro x hx
        rcases List.mem_map.mp hx with ⟨p, hp, hpx⟩
        have hTyped := map_entries_typed m T SmtType.Bool hmTy p hp
        have hCanP := map_entries_canonical m hCanParts.1 p hp
        rw [← hpx]
        exact hlT p.1 hTyped.1 hCanP.1
      have := nodup_subset_length _ lT hNodup hSub
      simpa using this
  refine List.mem_map.mpr ⟨(map_entries m).map Prod.fst, hKeysMem, ?_⟩
  have hRebuild := map_rebuild m T SmtType.Bool hmTy
  rw [← entries_eq_keys_map (map_entries m) hValuesTrue, ← hDefault,
    ← hRebuild]

-- === datatype covers ===

private theorem dt_resolve_nth_inv (dd : SmtDatatypeDecl) :
    ∀ (d : SmtDatatype) (k : Nat) (cr : SmtDatatypeCons),
      dt_nth_cons (__smtx_dt_resolve d dd) k = some cr →
        ∃ c : SmtDatatypeCons,
          dt_nth_cons d k = some c ∧ cr = __smtx_dtc_resolve c dd
  | SmtDatatype.null, k, cr, h => by
      simp [__smtx_dt_resolve, dt_nth_cons] at h
  | SmtDatatype.sum c d, 0, cr, h => by
      have : some (__smtx_dtc_resolve c dd) = some cr := by
        simpa [__smtx_dt_resolve, dt_nth_cons] using h
      injection this with h'
      exact ⟨c, rfl, h'.symm⟩
  | SmtDatatype.sum c d, Nat.succ k, cr, h => by
      have h' : dt_nth_cons (__smtx_dt_resolve d dd) k = some cr := by
        simpa [__smtx_dt_resolve, dt_nth_cons] using h
      rcases dt_resolve_nth_inv dd d k cr h' with ⟨c', hnth, hcr⟩
      exact ⟨c', by simpa [dt_nth_cons] using hnth, hcr⟩

private def covers_fields : List (List SmtValue) → List SmtType → Prop
  | [], [] => True
  | L :: Ls, U :: Us =>
      (∀ v : SmtValue, __smtx_typeof_value v = U →
        __smtx_value_canonical v = true → v ∈ L) ∧
      covers_fields Ls Us
  | _, _ => False

private def arg_lists : List (List SmtValue) → List (List SmtValue)
  | [] => [[]]
  | L :: Ls => L.flatMap (fun v => (arg_lists Ls).map (v :: ·))

private theorem arg_lists_complete :
    ∀ (Ls : List (List SmtValue)) (Us : List SmtType)
      (vs : List SmtValue),
      covers_fields Ls Us →
      list_typed_canonical vs Us →
      vs ∈ arg_lists Ls
  | [], [], [], _, _ => by
      simp [arg_lists]
  | [], [], v :: vs, _, hTyped => by
      simp [list_typed_canonical] at hTyped
  | [], U :: Us, vs, hCov, _ => by
      simp [covers_fields] at hCov
  | L :: Ls, [], vs, hCov, _ => by
      simp [covers_fields] at hCov
  | L :: Ls, U :: Us, [], _, hTyped => by
      simp [list_typed_canonical] at hTyped
  | L :: Ls, U :: Us, v :: vs, hCov, hTyped => by
      have hCovParts := hCov
      simp only [covers_fields] at hCovParts
      have hTypedParts := hTyped
      simp only [list_typed_canonical] at hTypedParts
      have hHead : v ∈ L :=
        hCovParts.1 v hTypedParts.1.1 hTypedParts.1.2.2
      have hTail :=
        arg_lists_complete Ls Us vs hCovParts.2 hTypedParts.2
      simp only [arg_lists, List.mem_flatMap, List.mem_map]
      exact ⟨v, hHead, vs, hTail, rfl⟩

private theorem cons_covers_exist
    (dd : SmtDatatypeDecl) (B0 : SmtDatatypeDecl)
    (hDecl : __smtx_decl_wf_rec dd dd = true)
    (hInv : ∀ r : native_String, __smtx_dd_has_dt r B0 = true →
      ∃ l : List SmtValue, ∀ v : SmtValue,
        __smtx_typeof_value v = SmtType.Datatype r dd →
        __smtx_value_canonical v = true → v ∈ l)
    (hGround : ∀ F : SmtType,
      (∀ r : native_String, F ≠ SmtType.TypeRef r) →
      sizeOf F < sizeOf dd →
      native_inhabited_type F = true →
      __smtx_type_wf_rec F = true →
      __smtx_is_finite_type F = true →
      ∃ l : List SmtValue, ∀ v : SmtValue,
        __smtx_typeof_value v = F →
        __smtx_value_canonical v = true → v ∈ l) :
    ∀ c : SmtDatatypeCons,
      (∀ F ∈ dtc_fields c, sizeOf F < sizeOf dd) →
      __smtx_datatype_cons_bounded false c B0 = true →
      __smtx_dt_cons_wf_rec dd c = true →
      ∃ Ls : List (List SmtValue),
        covers_fields Ls ((dtc_fields c).map (resolve_ty dd))
  | SmtDatatypeCons.unit, _, _, _ => ⟨[], by simp [dtc_fields, covers_fields]⟩
  | SmtDatatypeCons.cons F c, hSize, hBnd, hWf => by
      have hFieldBnd : __smtx_field_type_bounded false F B0 = true := by
        simp only [__smtx_datatype_cons_bounded, native_and,
          Bool.and_eq_true] at hBnd
        exact hBnd.1
      have hTailBnd : __smtx_datatype_cons_bounded false c B0 = true := by
        simp only [__smtx_datatype_cons_bounded, native_and,
          Bool.and_eq_true] at hBnd
        exact hBnd.2
      have hTailWf : __smtx_dt_cons_wf_rec dd c = true := by
        cases F <;>
          simp [__smtx_dt_cons_wf_rec, native_and] at hWf <;>
            first
              | exact hWf.2
              | exact hWf.2.2
      have hHead :
          ∃ L : List SmtValue, ∀ v : SmtValue,
            __smtx_typeof_value v = resolve_ty dd F →
            __smtx_value_canonical v = true → v ∈ L := by
        by_cases hRef : ∃ r : native_String, F = SmtType.TypeRef r
        · rcases hRef with ⟨r, rfl⟩
          have hrMem : __smtx_dd_has_dt r B0 = true := by
            simpa [__smtx_field_type_bounded] using hFieldBnd
          rcases hInv r hrMem with ⟨L, hL⟩
          exact ⟨L, by simpa [resolve_ty] using hL⟩
        · have hRef' : ∀ r : native_String, F ≠ SmtType.TypeRef r := by
            intro r hr
            exact hRef ⟨r, hr⟩
          have hFWf := resolved_field_inh_wf dd hDecl
            (SmtDatatypeCons.cons F c) hWf F (by simp [dtc_fields])
          rw [resolve_ty_ground dd F hRef'] at hFWf
          have hFFin : __smtx_is_finite_type F = true := by
            have hBnd' : __smtx_type_bounded false F = true := by
              cases F <;> first
                | exact absurd rfl (hRef' _)
                | simpa [__smtx_field_type_bounded] using hFieldBnd
            simpa [__smtx_is_finite_type] using hBnd'
          rcases hGround F hRef' (hSize F (by simp [dtc_fields]))
              hFWf.1 hFWf.2 hFFin with ⟨L, hL⟩
          exact ⟨L, by
            rw [resolve_ty_ground dd F hRef']
            exact hL⟩
      rcases hHead with ⟨L, hL⟩
      rcases cons_covers_exist dd B0 hDecl hInv hGround c
          (fun F' hF' => hSize F' (by simp [dtc_fields, hF']))
          hTailBnd hTailWf with ⟨Ls, hLs⟩
      refine ⟨L :: Ls, ?_⟩
      simp only [dtc_fields, List.map_cons, covers_fields]
      exact ⟨hL, hLs⟩

private theorem dt_spine_covers
    (t : native_String) (dd : SmtDatatypeDecl) (B0 : SmtDatatypeDecl)
    (hDecl : __smtx_decl_wf_rec dd dd = true)
    (hInv : ∀ r : native_String, __smtx_dd_has_dt r B0 = true →
      ∃ l : List SmtValue, ∀ v : SmtValue,
        __smtx_typeof_value v = SmtType.Datatype r dd →
        __smtx_value_canonical v = true → v ∈ l)
    (hGround : ∀ F : SmtType,
      (∀ r : native_String, F ≠ SmtType.TypeRef r) →
      sizeOf F < sizeOf dd →
      native_inhabited_type F = true →
      __smtx_type_wf_rec F = true →
      __smtx_is_finite_type F = true →
      ∃ l : List SmtValue, ∀ v : SmtValue,
        __smtx_typeof_value v = F →
        __smtx_value_canonical v = true → v ∈ l) :
    ∀ (d : SmtDatatype) (k0 : Nat),
      (∀ (j : Nat) (c : SmtDatatypeCons), dt_nth_cons d j = some c →
        ∀ F ∈ dtc_fields c, sizeOf F < sizeOf dd) →
      __smtx_datatype_bounded false d B0 = true →
      __smtx_dt_wf_rec dd d = true →
      ∃ cover : List SmtValue,
        ∀ (j : Nat) (c : SmtDatatypeCons) (vs : List SmtValue),
          dt_nth_cons d j = some c →
          list_typed_canonical vs ((dtc_fields c).map (resolve_ty dd)) →
          build_spine (SmtValue.DtCons t dd (k0 + j)) vs ∈ cover
  | SmtDatatype.null, k0, _, _, _ =>
      ⟨[], by
        intro j c vs hnth
        simp [dt_nth_cons] at hnth⟩
  | SmtDatatype.sum c rest, k0, hSizeAll, hBnd, hWf => by
      have hConsBnd : __smtx_datatype_cons_bounded false c B0 = true :=
        bounded_datatype_cons (SmtDatatype.sum c rest) 0 c rfl hBnd
      have hConsWf : __smtx_dt_cons_wf_rec dd c = true := by
        simp only [__smtx_dt_wf_rec, native_and, Bool.and_eq_true] at hWf
        exact hWf.1
      have hRestBnd : __smtx_datatype_bounded false rest B0 = true := by
        cases rest with
        | null => simp [__smtx_datatype_bounded, native_not]
        | sum c2 d2 =>
            simp only [__smtx_datatype_bounded, native_and, native_not,
              Bool.and_eq_true] at hBnd
            exact hBnd.2.2
      have hRestWf : __smtx_dt_wf_rec dd rest = true := by
        simp only [__smtx_dt_wf_rec, native_and, Bool.and_eq_true] at hWf
        exact hWf.2
      rcases cons_covers_exist dd B0 hDecl hInv hGround c
          (hSizeAll 0 c rfl) hConsBnd hConsWf with ⟨Ls, hLs⟩
      rcases dt_spine_covers t dd B0 hDecl hInv hGround rest (k0 + 1)
          (fun j c' hnth => hSizeAll (Nat.succ j) c'
            (by simpa [dt_nth_cons] using hnth))
          hRestBnd hRestWf with ⟨coverRest, hRest⟩
      refine ⟨(arg_lists Ls).map
        (build_spine (SmtValue.DtCons t dd k0)) ++ coverRest, ?_⟩
      intro j c' vs hnth hTyped
      cases j with
      | zero =>
          have hc : c = c' := by simpa [dt_nth_cons] using hnth
          subst c'
          have hMem := arg_lists_complete Ls _ vs hLs hTyped
          exact List.mem_append.mpr (Or.inl (List.mem_map.mpr
            ⟨vs, hMem, by simp⟩))
      | succ j' =>
          have hnth' : dt_nth_cons rest j' = some c' := by
            simpa [dt_nth_cons] using hnth
          have := hRest j' c' vs hnth' hTyped
          have hIdx : k0 + Nat.succ j' = (k0 + 1) + j' := by omega
          rw [hIdx]
          exact List.mem_append.mpr (Or.inr this)

/--
**Finite soundness** (statement 1): the typed canonical values of a
well-formed inhabited finite type are covered by a list.
-/
theorem finite_type_enumerable
    (A : SmtType)
    (hInh : native_inhabited_type A = true)
    (hRec : __smtx_type_wf_rec A = true)
    (hFin : __smtx_is_finite_type A = true) :
    ∃ l : List SmtValue, ∀ v : SmtValue,
      __smtx_typeof_value v = A →
      __smtx_value_canonical v = true → v ∈ l := by
  cases A with
  | None =>
      simp [__smtx_type_wf_rec] at hRec
  | RegLan =>
      simp [__smtx_type_wf_rec] at hRec
  | TypeRef t =>
      simp [__smtx_type_wf_rec] at hRec
  | FunType T U =>
      simp [__smtx_type_wf_rec] at hRec
  | DtcAppType T U =>
      simp [__smtx_type_wf_rec] at hRec
  | Int =>
      simp [__smtx_is_finite_type, __smtx_type_bounded] at hFin
  | Real =>
      simp [__smtx_is_finite_type, __smtx_type_bounded] at hFin
  | Seq T =>
      simp [__smtx_is_finite_type, __smtx_type_bounded] at hFin
  | USort u =>
      simp [__smtx_is_finite_type, __smtx_type_bounded] at hFin
  | Bool =>
      refine ⟨[SmtValue.Boolean false, SmtValue.Boolean true], ?_⟩
      intro v hTy hCan
      rcases typed_bool_shape v hTy with ⟨b, rfl⟩
      cases b <;> simp
  | Char =>
      refine ⟨(List.range 196608).map (fun c => SmtValue.Char c), ?_⟩
      intro v hTy hCan
      rcases typed_char_shape v hTy with ⟨c, rfl⟩
      have hValid : native_char_valid c = true := by
        by_cases hc : native_char_valid c = true
        · exact hc
        · simp [__smtx_typeof_value, native_ite, hc] at hTy
      have hLt : c < 196608 := by
        simpa [native_char_valid] using hValid
      exact List.mem_map.mpr ⟨c, List.mem_range.mpr hLt, rfl⟩
  | BitVec w =>
      refine ⟨(List.range (2 ^ w)).map
        (fun n => SmtValue.Binary (Int.ofNat w) (Int.ofNat n)), ?_⟩
      intro v hTy hCan
      rcases typed_bitvec_shape v w hTy with ⟨wi, n, rfl⟩
      by_cases hc :
          (native_and (native_zleq 0 wi)
            (native_zeq n (native_mod_total n (native_int_pow2 wi)))) = true
      · have hBV :
            SmtType.BitVec (native_int_to_nat wi) = SmtType.BitVec w := by
          simpa [__smtx_typeof_value, native_ite, hc] using hTy
        injection hBV with hw
        have hParts :
            native_zleq 0 wi = true ∧
              native_zeq n
                (native_mod_total n (native_int_pow2 wi)) = true := by
          simpa [native_and] using hc
        have hwiNonneg : (0 : Int) ≤ wi := by
          simpa [native_zleq] using hParts.1
        have hwiEq : wi = Int.ofNat w := by
          have hto := Int.toNat_of_nonneg hwiNonneg
          simp only [native_int_to_nat] at hw
          rw [← hto, hw]
          rfl
        subst hwiEq
        have hPow : native_int_pow2 (Int.ofNat w) = (2 : Int) ^ w := by
          have hnot : ¬ ((w : Int) < 0) := by omega
          simp [native_int_pow2, native_zexp_total, hnot]
        have hnMod : n = n % (2 : Int) ^ w := by
          have := hParts.2
          rw [hPow] at this
          simp only [native_zeq, native_mod_total] at this
          exact of_decide_eq_true this
        have hPowPos : (0 : Int) < 2 ^ w := by
          exact_mod_cast Nat.pow_pos (show 0 < 2 by decide) (n := w)
        have hnNonneg : 0 ≤ n := by
          rw [hnMod]
          exact Int.emod_nonneg n (by omega)
        have hnLt : n < 2 ^ w := by
          rw [hnMod]
          exact Int.emod_lt_of_pos n hPowPos
        have hCast : (((2 : Nat) ^ w : Nat) : Int) = (2 : Int) ^ w := by
          rw [Int.natCast_pow]
          rfl
        have hToNat : (↑n.toNat : Int) = n := Int.toNat_of_nonneg hnNonneg
        have hnNat : n.toNat < 2 ^ w := by
          refine Int.ofNat_lt.mp ?_
          rw [hToNat, hCast]
          exact hnLt
        refine List.mem_map.mpr ⟨n.toNat, List.mem_range.mpr hnNat, ?_⟩
        have : Int.ofNat n.toNat = n := Int.toNat_of_nonneg hnNonneg
        rw [this]
      · simp [__smtx_typeof_value, native_ite, hc] at hTy
  | Set T =>
      have hRecParts :
          native_inhabited_type T = true ∧
            __smtx_type_wf_rec T = true := by
        have h := hRec
        simp [__smtx_type_wf_rec, native_and] at h
        exact h
      have hTFin : __smtx_is_finite_type T = true := by
        simpa [__smtx_is_finite_type, __smtx_type_bounded, native_and,
          native_not] using hFin
      rcases finite_type_enumerable T hRecParts.1 hRecParts.2 hTFin with
        ⟨lT, hlT⟩
      exact set_cover_exists T lT hlT
  | Map T U =>
      have hRecParts :
          native_inhabited_type T = true ∧
            __smtx_type_wf_rec T = true ∧
              native_inhabited_type U = true ∧
                __smtx_type_wf_rec U = true := by
        have h := hRec
        simp [__smtx_type_wf_rec, native_and] at h
        exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩
      by_cases hUUnit : __smtx_is_unit_type U = true
      · -- unit range: the whole map type is a unit type
        have hMapUnit : __smtx_is_unit_type (SmtType.Map T U) = true := by
          have hU : __smtx_type_bounded true U = true := by
            simpa [__smtx_is_unit_type] using hUUnit
          simp [__smtx_is_unit_type, __smtx_type_bounded, native_or,
            native_and, native_not, hU]
        refine ⟨[__smtx_type_default (SmtType.Map T U)], ?_⟩
        intro v hTy hCan
        have := unit_type_values_default (SmtType.Map T U) hInh hRec
          hMapUnit v hTy hCan
        simp [this]
      · have hUUnitF : __smtx_is_unit_type U = false := by
          cases h : __smtx_is_unit_type U
          · rfl
          · exact absurd h hUUnit
        have hTFin : __smtx_is_finite_type T = true ∧
            __smtx_is_finite_type U = true := by
          have h := hFin
          simp only [__smtx_is_finite_type, __smtx_type_bounded, native_or,
            native_and, native_not, Bool.or_eq_true, Bool.and_eq_true,
            Bool.not_false] at h
          rcases h with hUnit | ⟨_, hT, hU⟩
          · exact absurd (by simpa [__smtx_is_unit_type] using hUnit)
              hUUnit
          · exact ⟨by simpa [__smtx_is_finite_type] using hT,
              by simpa [__smtx_is_finite_type] using hU⟩
        rcases finite_type_enumerable T hRecParts.1 hRecParts.2.1
            hTFin.1 with ⟨lT, hlT⟩
        rcases finite_type_enumerable U hRecParts.2.2.1 hRecParts.2.2.2
            hTFin.2 with ⟨lU, hlU⟩
        exact map_cover_exists T U lT lU hTFin.1 hlT hlU
  | Datatype s dd =>
      have hRecParts :
          __smtx_dd_has_dt s dd = true ∧
            __smtx_decl_wf_rec dd dd = true := by
        simpa [__smtx_type_wf_rec, native_and] using hRec
      have hUniq : dd_unique dd := dd_unique_of_decl_wf dd dd hRecParts.2
      have hFixMem :
          __smtx_dd_has_dt s
            (__smtx_datatype_decl_bounded false dd dd
              SmtDatatypeDecl.nil) = true := by
        rw [is_finite_datatype_eq] at hFin
        exact hFin
      refine decl_bounded_payload false dd hUniq
        (fun t => ∃ l : List SmtValue, ∀ v : SmtValue,
          __smtx_typeof_value v = SmtType.Datatype t dd →
          __smtx_value_canonical v = true → v ∈ l)
        ?_ s hFixMem
      intro t hMemDD B0 hBnd hInvB
      have hDtWf : __smtx_dt_wf_rec dd (__smtx_dd_lookup t dd) = true :=
        decl_wf_rec_lookup_local t dd dd hMemDD hRecParts.2
      have hGround : ∀ F : SmtType,
          (∀ r : native_String, F ≠ SmtType.TypeRef r) →
          sizeOf F < sizeOf dd →
          native_inhabited_type F = true →
          __smtx_type_wf_rec F = true →
          __smtx_is_finite_type F = true →
          ∃ l : List SmtValue, ∀ v : SmtValue,
            __smtx_typeof_value v = F →
            __smtx_value_canonical v = true → v ∈ l := by
        intro F hRef hMeasure hFInh hFRec hFFin
        exact finite_type_enumerable F hFInh hFRec hFFin
      have hSizeAll : ∀ (j : Nat) (c : SmtDatatypeCons),
          dt_nth_cons (__smtx_dd_lookup t dd) j = some c →
          ∀ F ∈ dtc_fields c, sizeOf F < sizeOf dd := by
        intro j c hnth F hF
        have h1 := sizeOf_field_lt c F hF
        have h2 := sizeOf_nth_cons_lt (__smtx_dd_lookup t dd) j c hnth
        have h3 := sizeOf_lookup_lt t dd hMemDD
        omega
      rcases dt_spine_covers t dd B0 hRecParts.2 hInvB hGround
          (__smtx_dd_lookup t dd) 0 hSizeAll hBnd hDtWf with
        ⟨cover, hCover⟩
      refine ⟨cover, ?_⟩
      intro v hTy hCan
      rcases datatype_typed_canonical_spine v t dd hTy hCan with
        ⟨k, cr, vs, hnth, hSpine, hTyped⟩
      rcases dt_resolve_nth_inv dd (__smtx_dd_lookup t dd) k cr hnth with
        ⟨c, hnthU, hcr⟩
      subst hcr
      have hTyped' :
          list_typed_canonical vs ((dtc_fields c).map (resolve_ty dd)) := by
        rw [← dtc_resolve_fields dd c]
        exact hTyped
      have := hCover k c vs hnthU hTyped'
      rw [hSpine]
      simpa using this
termination_by sizeOf A
decreasing_by
  all_goals subst A
  all_goals first
    | (rw [show sizeOf (SmtType.Set T) = 1 + sizeOf T by rfl]
       omega)
    | (rw [show sizeOf (SmtType.Map T U) = 1 + sizeOf T + sizeOf U by rfl]
       omega)
    | (rw [show sizeOf (SmtType.Datatype s dd) =
          1 + sizeOf s + sizeOf dd by rfl]
       omega)

end Smtm
