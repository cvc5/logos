module

public import Cpc.Proofs.Canonical.TypeDefaultBasic
import all Cpc.Proofs.Canonical.TypeDefaultBasic

public section

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Smtm

/-!
# The infinite-datatype pump

Builds arbitrarily large typed canonical values of infinite datatypes, against
the declaration-based datatype representation and the `__smtx_type_bounded`
finiteness fixpoint.

Part A (this section): complement characterization of the finiteness fixpoint
`__smtx_datatype_decl_bounded` — a declared datatype outside the fixpoint has
a constructor with a field that is itself outside the fixpoint (an unbounded
sibling reference or an unbounded ground type).

The fixpoint iterates `__smtx_datatype_decl_bounded_step` once per entry of
the declaration, starting from the empty accumulator.  We show the result is
saturated (one more step changes nothing, by a counting argument), that a
bounded body would have been added (monotonicity), and conclude.
-/

-- === subset order on accumulators (via name membership) ===

def SubDD (B B' : SmtDatatypeDecl) : Prop :=
  ∀ t : native_String,
    __smtx_dd_has_dt t B = true -> __smtx_dd_has_dt t B' = true

theorem subdd_cons (s : native_String) (d : SmtDatatype)
    (B : SmtDatatypeDecl) : SubDD B (SmtDatatypeDecl.cons s d B) := by
  intro t h
  simp [__smtx_dd_has_dt, native_or, h]

private def EqDD (B B' : SmtDatatypeDecl) : Prop :=
  ∀ t : native_String, __smtx_dd_has_dt t B = __smtx_dd_has_dt t B'

private theorem eqdd_refl (B : SmtDatatypeDecl) : EqDD B B :=
  fun _ => rfl

private theorem eqdd_symm {B B' : SmtDatatypeDecl} (h : EqDD B B') : EqDD B' B :=
  fun t => (h t).symm

private theorem eqdd_trans {B1 B2 B3 : SmtDatatypeDecl}
    (h12 : EqDD B1 B2) (h23 : EqDD B2 B3) : EqDD B1 B3 :=
  fun t => (h12 t).trans (h23 t)

-- === monotonicity / congruence of boundedness in the accumulator ===

private theorem field_type_bounded_mono (u : native_Bool)
    {B B' : SmtDatatypeDecl} (hSub : SubDD B B') :
    ∀ T : SmtType,
      __smtx_field_type_bounded u T B = true ->
        __smtx_field_type_bounded u T B' = true := by
  intro T h
  cases T <;> simp [__smtx_field_type_bounded] at h ⊢ <;>
    first
      | exact hSub _ h
      | exact h

private theorem field_type_bounded_congr (u : native_Bool)
    {B B' : SmtDatatypeDecl} (hEq : EqDD B B') :
    ∀ T : SmtType,
      __smtx_field_type_bounded u T B = __smtx_field_type_bounded u T B' := by
  intro T
  cases T <;> simp [__smtx_field_type_bounded] <;> exact hEq _

private theorem dt_cons_bounded_mono (u : native_Bool)
    {B B' : SmtDatatypeDecl} (hSub : SubDD B B') :
    ∀ c : SmtDatatypeCons,
      __smtx_datatype_cons_bounded u c B = true ->
        __smtx_datatype_cons_bounded u c B' = true
  | SmtDatatypeCons.unit, h => by
      simp [__smtx_datatype_cons_bounded]
  | SmtDatatypeCons.cons T c, h => by
      simp [__smtx_datatype_cons_bounded, native_and] at h ⊢
      exact ⟨field_type_bounded_mono u hSub T h.1,
        dt_cons_bounded_mono u hSub c h.2⟩

private theorem dt_cons_bounded_congr (u : native_Bool)
    {B B' : SmtDatatypeDecl} (hEq : EqDD B B') :
    ∀ c : SmtDatatypeCons,
      __smtx_datatype_cons_bounded u c B = __smtx_datatype_cons_bounded u c B'
  | SmtDatatypeCons.unit => by
      simp [__smtx_datatype_cons_bounded]
  | SmtDatatypeCons.cons T c => by
      simp [__smtx_datatype_cons_bounded, native_and,
        field_type_bounded_congr u hEq T, dt_cons_bounded_congr u hEq c]

theorem datatype_bounded_mono (u : native_Bool)
    {B B' : SmtDatatypeDecl} (hSub : SubDD B B') :
    ∀ d : SmtDatatype,
      __smtx_datatype_bounded u d B = true ->
        __smtx_datatype_bounded u d B' = true
  | SmtDatatype.null, h => by
      simpa [__smtx_datatype_bounded] using h
  | SmtDatatype.sum c SmtDatatype.null, h => by
      simp [__smtx_datatype_bounded] at h ⊢
      exact dt_cons_bounded_mono u hSub c h
  | SmtDatatype.sum c (SmtDatatype.sum c2 d2), h => by
      simp [__smtx_datatype_bounded, native_and] at h ⊢
      exact ⟨h.1, dt_cons_bounded_mono u hSub c h.2.1,
        datatype_bounded_mono u hSub (SmtDatatype.sum c2 d2) h.2.2⟩

private theorem datatype_bounded_congr (u : native_Bool)
    {B B' : SmtDatatypeDecl} (hEq : EqDD B B') :
    ∀ d : SmtDatatype,
      __smtx_datatype_bounded u d B = __smtx_datatype_bounded u d B'
  | SmtDatatype.null => by
      simp [__smtx_datatype_bounded]
  | SmtDatatype.sum c SmtDatatype.null => by
      simp [__smtx_datatype_bounded, dt_cons_bounded_congr u hEq c]
  | SmtDatatype.sum c (SmtDatatype.sum c2 d2) => by
      simp [__smtx_datatype_bounded, native_and,
        dt_cons_bounded_congr u hEq c,
        datatype_bounded_congr u hEq (SmtDatatype.sum c2 d2)]

-- === the step: growth, name provenance, congruence, addition ===

private theorem step_grows (u : native_Bool) :
    ∀ (dds B : SmtDatatypeDecl),
      SubDD B (__smtx_datatype_decl_bounded_step u dds B)
  | SmtDatatypeDecl.nil, B => by
      intro t h
      simpa [__smtx_datatype_decl_bounded_step] using h
  | SmtDatatypeDecl.cons sF dF ddR, B => by
      intro t h
      simp only [__smtx_datatype_decl_bounded_step]
      by_cases hCond :
          (native_and (native_not (__smtx_dd_has_dt sF B))
            (__smtx_datatype_bounded u dF B)) = true
      · rw [native_ite, if_pos hCond]
        exact step_grows u ddR (SmtDatatypeDecl.cons sF dF B) t
          (subdd_cons sF dF B t h)
      · rw [native_ite, if_neg hCond]
        exact step_grows u ddR B t h

private theorem step_names (u : native_Bool) :
    ∀ (dds B : SmtDatatypeDecl) (t : native_String),
      __smtx_dd_has_dt t (__smtx_datatype_decl_bounded_step u dds B) = true ->
        __smtx_dd_has_dt t B = true ∨ __smtx_dd_has_dt t dds = true
  | SmtDatatypeDecl.nil, B, t, h => by
      left
      simpa [__smtx_datatype_decl_bounded_step] using h
  | SmtDatatypeDecl.cons sF dF ddR, B, t, h => by
      simp only [__smtx_datatype_decl_bounded_step] at h
      by_cases hCond :
          (native_and (native_not (__smtx_dd_has_dt sF B))
            (__smtx_datatype_bounded u dF B)) = true
      · rw [native_ite, if_pos hCond] at h
        rcases step_names u ddR (SmtDatatypeDecl.cons sF dF B) t h with hIn | hTail
        · simp [__smtx_dd_has_dt, native_or] at hIn
          rcases hIn with hEq | hB
          · right
            simp [__smtx_dd_has_dt, native_or, hEq]
          · left
            exact hB
        · right
          simp [__smtx_dd_has_dt, native_or, hTail]
      · rw [native_ite, if_neg hCond] at h
        rcases step_names u ddR B t h with hB | hTail
        · left
          exact hB
        · right
          simp [__smtx_dd_has_dt, native_or, hTail]

private theorem step_congr (u : native_Bool) :
    ∀ (dds B B' : SmtDatatypeDecl),
      EqDD B B' ->
        EqDD (__smtx_datatype_decl_bounded_step u dds B)
          (__smtx_datatype_decl_bounded_step u dds B')
  | SmtDatatypeDecl.nil, B, B', hEq => by
      simpa [__smtx_datatype_decl_bounded_step] using hEq
  | SmtDatatypeDecl.cons sF dF ddR, B, B', hEq => by
      simp only [__smtx_datatype_decl_bounded_step]
      have hCondEq :
          (native_and (native_not (__smtx_dd_has_dt sF B))
            (__smtx_datatype_bounded u dF B)) =
          (native_and (native_not (__smtx_dd_has_dt sF B'))
            (__smtx_datatype_bounded u dF B')) := by
        rw [hEq sF, datatype_bounded_congr u hEq dF]
      by_cases hCond :
          (native_and (native_not (__smtx_dd_has_dt sF B))
            (__smtx_datatype_bounded u dF B)) = true
      · rw [native_ite, if_pos hCond, native_ite, if_pos (hCondEq ▸ hCond)]
        exact step_congr u ddR _ _ (by
          intro t
          simp [__smtx_dd_has_dt, native_or, hEq t])
      · rw [native_ite, if_neg hCond, native_ite,
          if_neg (fun h => hCond (hCondEq ▸ h))]
        exact step_congr u ddR B B' hEq

/--
If a name `t` occurs in the sweep list with body given by first-occurrence
lookup, and that body is bounded at the initial accumulator, then `t` is in
the accumulator after the sweep.
-/
private theorem step_adds (u : native_Bool) (t : native_String) :
    ∀ (dds B : SmtDatatypeDecl),
      __smtx_dd_has_dt t dds = true ->
      __smtx_datatype_bounded u (__smtx_dd_lookup t dds) B = true ->
        __smtx_dd_has_dt t (__smtx_datatype_decl_bounded_step u dds B) = true
  | SmtDatatypeDecl.nil, B, hMem, _hBnd => by
      simp [__smtx_dd_has_dt] at hMem
  | SmtDatatypeDecl.cons sF dF ddR, B, hMem, hBnd => by
      simp only [__smtx_datatype_decl_bounded_step]
      by_cases hs : native_streq t sF = true
      · -- this entry is (a first occurrence of) t
        have hLookup : __smtx_dd_lookup t (SmtDatatypeDecl.cons sF dF ddR) = dF := by
          simp [__smtx_dd_lookup, native_ite, hs]
        rw [hLookup] at hBnd
        by_cases hIn : __smtx_dd_has_dt sF B = true
        · -- already present: preserved through the rest of the sweep
          have hInT : __smtx_dd_has_dt t B = true := by
            have hts : t = sF := by simpa [native_streq] using hs
            rw [hts]
            exact hIn
          by_cases hCond :
              (native_and (native_not (__smtx_dd_has_dt sF B))
                (__smtx_datatype_bounded u dF B)) = true
          · rw [native_ite, if_pos hCond]
            exact step_grows u ddR (SmtDatatypeDecl.cons sF dF B) t
              (subdd_cons sF dF B t hInT)
          · rw [native_ite, if_neg hCond]
            exact step_grows u ddR B t hInT
        · -- newly added by this entry
          have hCond :
              (native_and (native_not (__smtx_dd_has_dt sF B))
                (__smtx_datatype_bounded u dF B)) = true := by
            have hInF : __smtx_dd_has_dt sF B = false := by
              cases h : __smtx_dd_has_dt sF B <;> simp [h] at hIn ⊢
            simp [native_and, native_not, hInF, hBnd]
          rw [native_ite, if_pos hCond]
          have hInCons :
              __smtx_dd_has_dt t (SmtDatatypeDecl.cons sF dF B) = true := by
            simp [__smtx_dd_has_dt, native_or, hs]
          exact step_grows u ddR (SmtDatatypeDecl.cons sF dF B) t hInCons
      · -- t lives in the tail of the sweep
        have hMemTail : __smtx_dd_has_dt t ddR = true := by
          simpa [__smtx_dd_has_dt, native_or, hs] using hMem
        have hLookupTail :
            __smtx_dd_lookup t (SmtDatatypeDecl.cons sF dF ddR) =
              __smtx_dd_lookup t ddR := by
          simp [__smtx_dd_lookup, native_ite, hs]
        rw [hLookupTail] at hBnd
        by_cases hCond :
            (native_and (native_not (__smtx_dd_has_dt sF B))
              (__smtx_datatype_bounded u dF B)) = true
        · rw [native_ite, if_pos hCond]
          exact step_adds u t ddR (SmtDatatypeDecl.cons sF dF B) hMemTail
            (datatype_bounded_mono u (subdd_cons sF dF B) _ hBnd)
        · rw [native_ite, if_neg hCond]
          exact step_adds u t ddR B hMemTail hBnd

-- === counting names for saturation ===

private def dd_len : SmtDatatypeDecl -> Nat
  | SmtDatatypeDecl.nil => 0
  | SmtDatatypeDecl.cons _ _ rest => dd_len rest + 1

private def dd_count (B : SmtDatatypeDecl) : SmtDatatypeDecl -> Nat
  | SmtDatatypeDecl.nil => 0
  | SmtDatatypeDecl.cons t _ rest =>
      (if __smtx_dd_has_dt t B = true then 1 else 0) + dd_count B rest

private theorem dd_count_le_len (B : SmtDatatypeDecl) :
    ∀ dd : SmtDatatypeDecl, dd_count B dd ≤ dd_len dd
  | SmtDatatypeDecl.nil => Nat.le_refl _
  | SmtDatatypeDecl.cons t d rest => by
      have := dd_count_le_len B rest
      by_cases h : __smtx_dd_has_dt t B = true <;>
        simp [dd_count, dd_len, h] <;> omega

private theorem dd_count_mono {B B' : SmtDatatypeDecl} (hSub : SubDD B B') :
    ∀ dd : SmtDatatypeDecl, dd_count B dd ≤ dd_count B' dd
  | SmtDatatypeDecl.nil => Nat.le_refl _
  | SmtDatatypeDecl.cons t d rest => by
      have hRest := dd_count_mono hSub rest
      by_cases h : __smtx_dd_has_dt t B = true
      · have h' := hSub t h
        simp [dd_count, h, h']
        omega
      · by_cases h' : __smtx_dd_has_dt t B' = true <;>
          simp [dd_count, h, h'] <;> omega

private theorem dd_count_lt {B B' : SmtDatatypeDecl} (hSub : SubDD B B')
    (t : native_String)
    (hOld : __smtx_dd_has_dt t B = false)
    (hNew : __smtx_dd_has_dt t B' = true) :
    ∀ dd : SmtDatatypeDecl,
      __smtx_dd_has_dt t dd = true ->
        dd_count B dd < dd_count B' dd
  | SmtDatatypeDecl.nil, hMem => by
      simp [__smtx_dd_has_dt] at hMem
  | SmtDatatypeDecl.cons s d rest, hMem => by
      by_cases hs : native_streq t s = true
      · have hts : t = s := by simpa [native_streq] using hs
        subst s
        have hRest := dd_count_mono hSub rest
        simp [dd_count, hOld, hNew]
        omega
      · have hMemTail : __smtx_dd_has_dt t rest = true := by
          simpa [__smtx_dd_has_dt, native_or, hs] using hMem
        have hRest := dd_count_lt hSub t hOld hNew rest hMemTail
        by_cases hsB : __smtx_dd_has_dt s B = true
        · have hsB' := hSub s hsB
          simp [dd_count, hsB, hsB']
          omega
        · by_cases hsB' : __smtx_dd_has_dt s B' = true <;>
            simp [dd_count, hsB, hsB'] <;> omega

private def StableDD (u : native_Bool) (dd B : SmtDatatypeDecl) : Prop :=
  EqDD (__smtx_datatype_decl_bounded_step u dd B) B

private theorem stable_congr {u : native_Bool} {dd B B' : SmtDatatypeDecl}
    (hEq : EqDD B B') (hStable : StableDD u dd B) : StableDD u dd B' :=
  eqdd_trans (eqdd_trans (step_congr u dd B' B (eqdd_symm hEq)) hStable) hEq

private theorem step_stable_or_grow (u : native_Bool) (dd : SmtDatatypeDecl) :
    ∀ B : SmtDatatypeDecl,
      StableDD u dd B ∨
        dd_count B dd < dd_count (__smtx_datatype_decl_bounded_step u dd B) dd := by
  intro B
  classical
  by_cases hStable : StableDD u dd B
  · exact Or.inl hStable
  · right
    have hDiff :
        ∃ t : native_String,
          ¬ (__smtx_dd_has_dt t (__smtx_datatype_decl_bounded_step u dd B) =
              __smtx_dd_has_dt t B) :=
      Classical.byContradiction (fun hAll =>
        hStable (fun t =>
          Classical.byContradiction (fun hne => hAll ⟨t, hne⟩)))
    rcases hDiff with ⟨t, hNe⟩
    have hSub := step_grows u dd B
    have hOld : __smtx_dd_has_dt t B = false := by
      cases hB : __smtx_dd_has_dt t B
      · rfl
      · exact absurd (by rw [hSub t hB, hB]) hNe
    have hNew :
        __smtx_dd_has_dt t (__smtx_datatype_decl_bounded_step u dd B) = true := by
      cases hFB : __smtx_dd_has_dt t (__smtx_datatype_decl_bounded_step u dd B)
      · exact absurd (by rw [hFB, hOld]) hNe
      · rfl
    have hMem : __smtx_dd_has_dt t dd = true := by
      rcases step_names u dd B t hNew with hB | hdd
      · rw [hB] at hOld
        cases hOld
      · exact hdd
    exact dd_count_lt hSub t hOld hNew dd hMem

private theorem decl_bounded_congr (u : native_Bool) (dd : SmtDatatypeDecl) :
    ∀ (ddC : SmtDatatypeDecl) {B B' : SmtDatatypeDecl},
      EqDD B B' ->
        EqDD (__smtx_datatype_decl_bounded u ddC dd B)
          (__smtx_datatype_decl_bounded u ddC dd B')
  | SmtDatatypeDecl.nil, B, B', hEq => by
      simpa [__smtx_datatype_decl_bounded] using hEq
  | SmtDatatypeDecl.cons sC dC ddC, B, B', hEq => by
      simp only [__smtx_datatype_decl_bounded]
      exact decl_bounded_congr u dd ddC (step_congr u dd B B' hEq)

private theorem decl_bounded_stable_fix (u : native_Bool) (dd : SmtDatatypeDecl) :
    ∀ (ddC : SmtDatatypeDecl) {B : SmtDatatypeDecl},
      StableDD u dd B ->
        EqDD (__smtx_datatype_decl_bounded u ddC dd B) B
  | SmtDatatypeDecl.nil, B, hStable => by
      simpa [__smtx_datatype_decl_bounded] using eqdd_refl B
  | SmtDatatypeDecl.cons sC dC ddC, B, hStable => by
      simp only [__smtx_datatype_decl_bounded]
      have hStepEq : EqDD (__smtx_datatype_decl_bounded_step u dd B) B := hStable
      exact eqdd_trans
        (decl_bounded_congr u dd ddC hStepEq)
        (decl_bounded_stable_fix u dd ddC hStable)

private theorem decl_bounded_stable_or_count (u : native_Bool) (dd : SmtDatatypeDecl) :
    ∀ (ddC : SmtDatatypeDecl) (B : SmtDatatypeDecl),
      StableDD u dd (__smtx_datatype_decl_bounded u ddC dd B) ∨
        dd_len ddC + dd_count B dd ≤
          dd_count (__smtx_datatype_decl_bounded u ddC dd B) dd
  | SmtDatatypeDecl.nil, B => by
      right
      simp [__smtx_datatype_decl_bounded, dd_len]
  | SmtDatatypeDecl.cons sC dC ddC, B => by
      simp only [__smtx_datatype_decl_bounded]
      rcases step_stable_or_grow u dd B with hStable | hGrow
      · left
        have hStepStable :
            StableDD u dd (__smtx_datatype_decl_bounded_step u dd B) :=
          stable_congr (eqdd_symm hStable) hStable
        exact stable_congr
          (eqdd_symm (decl_bounded_stable_fix u dd ddC hStepStable))
          hStepStable
      · rcases decl_bounded_stable_or_count u dd ddC
            (__smtx_datatype_decl_bounded_step u dd B) with hStable | hCount
        · exact Or.inl hStable
        · right
          simp only [dd_len]
          omega

/-- The finiteness fixpoint is saturated: one more step changes nothing. -/
private theorem decl_bounded_saturated (u : native_Bool) (dd : SmtDatatypeDecl) :
    StableDD u dd
      (__smtx_datatype_decl_bounded u dd dd SmtDatatypeDecl.nil) := by
  rcases decl_bounded_stable_or_count u dd dd SmtDatatypeDecl.nil with
    hStable | hCount
  · exact hStable
  · -- the count has reached the maximum, so a further step cannot grow it
    rcases step_stable_or_grow u dd
        (__smtx_datatype_decl_bounded u dd dd SmtDatatypeDecl.nil) with
      hStable | hGrow
    · exact hStable
    · exfalso
      have hLe := dd_count_le_len
        (__smtx_datatype_decl_bounded_step u dd
          (__smtx_datatype_decl_bounded u dd dd SmtDatatypeDecl.nil)) dd
      omega

/--
Complement characterization: a declared name outside the finiteness fixpoint
has an unbounded body at the fixpoint.
-/
private theorem unbounded_lookup_of_not_fix (u : native_Bool)
    (dd : SmtDatatypeDecl) (s : native_String)
    (hMem : __smtx_dd_has_dt s dd = true)
    (hNot :
      __smtx_dd_has_dt s
        (__smtx_datatype_decl_bounded u dd dd SmtDatatypeDecl.nil) = false) :
    __smtx_datatype_bounded u (__smtx_dd_lookup s dd)
      (__smtx_datatype_decl_bounded u dd dd SmtDatatypeDecl.nil) = false := by
  cases hBnd :
      __smtx_datatype_bounded u (__smtx_dd_lookup s dd)
        (__smtx_datatype_decl_bounded u dd dd SmtDatatypeDecl.nil)
  · rfl
  · exfalso
    have hAdded :=
      step_adds u s dd
        (__smtx_datatype_decl_bounded u dd dd SmtDatatypeDecl.nil) hMem hBnd
    have hStable := decl_bounded_saturated u dd
    rw [hStable s] at hAdded
    rw [hAdded] at hNot
    cases hNot

/-!
## Part B: constructor extraction and spine machinery

From an unbounded body, extract a constructor with an unbounded field; relate
constructor fields to the value-level constructor type chain; build, type and
size constructor-application spines.
-/

def dt_nth_cons : SmtDatatype -> Nat -> Option SmtDatatypeCons
  | SmtDatatype.sum c _, 0 => some c
  | SmtDatatype.sum _ d, Nat.succ n => dt_nth_cons d n
  | SmtDatatype.null, _ => none

def dtc_fields : SmtDatatypeCons -> List SmtType
  | SmtDatatypeCons.unit => []
  | SmtDatatypeCons.cons T c => T :: dtc_fields c

/-- Single-field resolution: what `__smtx_dtc_resolve` does to one field. -/
def resolve_ty (dd : SmtDatatypeDecl) : SmtType -> SmtType
  | SmtType.TypeRef s => SmtType.Datatype s dd
  | T => T

theorem dtc_resolve_fields (dd : SmtDatatypeDecl) :
    ∀ c : SmtDatatypeCons,
      dtc_fields (__smtx_dtc_resolve c dd) =
        (dtc_fields c).map (resolve_ty dd)
  | SmtDatatypeCons.unit => by
      simp [__smtx_dtc_resolve, dtc_fields]
  | SmtDatatypeCons.cons T c => by
      cases T <;>
        simp [__smtx_dtc_resolve, dtc_fields, resolve_ty,
          dtc_resolve_fields dd c]

private theorem unbounded_datatype_has_unbounded_cons
    {B : SmtDatatypeDecl} :
    ∀ d : SmtDatatype,
      __smtx_datatype_bounded false d B = false ->
        ∃ (k : Nat) (c : SmtDatatypeCons),
          dt_nth_cons d k = some c ∧
            __smtx_datatype_cons_bounded false c B = false
  | SmtDatatype.null, h => by
      simp [__smtx_datatype_bounded, native_not] at h
  | SmtDatatype.sum c SmtDatatype.null, h => by
      refine ⟨0, c, rfl, ?_⟩
      simpa [__smtx_datatype_bounded] using h
  | SmtDatatype.sum c (SmtDatatype.sum c2 d2), h => by
      simp [__smtx_datatype_bounded, native_and, native_not] at h
      cases hc : __smtx_datatype_cons_bounded false c B with
      | false =>
          exact ⟨0, c, rfl, hc⟩
      | true =>
          rcases unbounded_datatype_has_unbounded_cons
              (SmtDatatype.sum c2 d2) (h hc) with ⟨k, c', hnth, hc'⟩
          exact ⟨Nat.succ k, c', by simpa [dt_nth_cons] using hnth, hc'⟩

theorem unbounded_cons_has_unbounded_field
    {u : native_Bool} {B : SmtDatatypeDecl} :
    ∀ c : SmtDatatypeCons,
      __smtx_datatype_cons_bounded u c B = false ->
        ∃ (pre : List SmtType) (F : SmtType) (post : List SmtType),
          dtc_fields c = pre ++ F :: post ∧
            __smtx_field_type_bounded u F B = false
  | SmtDatatypeCons.unit, h => by
      simp [__smtx_datatype_cons_bounded] at h
  | SmtDatatypeCons.cons T c, h => by
      simp [__smtx_datatype_cons_bounded, native_and] at h
      cases hT : __smtx_field_type_bounded u T B with
      | false =>
          exact ⟨[], T, dtc_fields c, by simp [dtc_fields], hT⟩
      | true =>
          rcases unbounded_cons_has_unbounded_field c (h hT) with
            ⟨pre, F, post, hEq, hF⟩
          exact ⟨T :: pre, F, post, by simp [dtc_fields, hEq], hF⟩

-- === well-formedness transport to resolved fields ===

theorem decl_wf_rec_lookup_local
    (s : native_String) (dd : SmtDatatypeDecl) :
    ∀ dd2, __smtx_dd_has_dt s dd2 = true →
      __smtx_decl_wf_rec dd dd2 = true →
      __smtx_dt_wf_rec dd (__smtx_dd_lookup s dd2) = true
  | SmtDatatypeDecl.nil, hHas, _ => by
      simp [__smtx_dd_has_dt] at hHas
  | SmtDatatypeDecl.cons s2 d2 dd2, hHas, h => by
      by_cases hs : native_streq s s2 = true
      · have hDt : __smtx_dt_wf_rec dd d2 = true := by
          simp only [__smtx_decl_wf_rec, native_and, Bool.and_eq_true] at h
          exact h.1
        simpa [__smtx_dd_lookup, native_ite, hs] using hDt
      · have hHasTail : __smtx_dd_has_dt s dd2 = true := by
          simpa [__smtx_dd_has_dt, native_or, hs] using hHas
        have hTail : __smtx_decl_wf_rec dd dd2 = true := by
          simp only [__smtx_decl_wf_rec, native_and, Bool.and_eq_true] at h
          exact h.2.2.1
        simpa [__smtx_dd_lookup, native_ite, hs] using
          decl_wf_rec_lookup_local s dd dd2 hHasTail hTail

theorem decl_wf_rec_inh
    (s : native_String) (dd : SmtDatatypeDecl) :
    ∀ dd2, __smtx_dd_has_dt s dd2 = true →
      __smtx_decl_wf_rec dd dd2 = true →
      native_inhabited_type (SmtType.Datatype s dd) = true
  | SmtDatatypeDecl.nil, hHas, _ => by
      simp [__smtx_dd_has_dt] at hHas
  | SmtDatatypeDecl.cons s2 d2 dd2, hHas, h => by
      by_cases hs : native_streq s s2 = true
      · have hss2 : s = s2 := by simpa [native_streq] using hs
        subst s2
        simp only [__smtx_decl_wf_rec, native_and, Bool.and_eq_true] at h
        exact h.2.1
      · have hHasTail : __smtx_dd_has_dt s dd2 = true := by
          simpa [__smtx_dd_has_dt, native_or, hs] using hHas
        have hTail : __smtx_decl_wf_rec dd dd2 = true := by
          simp only [__smtx_decl_wf_rec, native_and, Bool.and_eq_true] at h
          exact h.2.2.1
        exact decl_wf_rec_inh s dd dd2 hHasTail hTail

theorem dt_wf_nth_cons (dd : SmtDatatypeDecl) :
    ∀ (d : SmtDatatype) (k : Nat) (c : SmtDatatypeCons),
      dt_nth_cons d k = some c ->
        __smtx_dt_wf_rec dd d = true ->
        __smtx_dt_cons_wf_rec dd c = true
  | SmtDatatype.null, k, c, hnth, _ => by
      simp [dt_nth_cons] at hnth
  | SmtDatatype.sum cF dF, 0, c, hnth, hWf => by
      have hc : cF = c := by simpa [dt_nth_cons] using hnth
      subst c
      simp only [__smtx_dt_wf_rec, native_and, Bool.and_eq_true] at hWf
      exact hWf.1
  | SmtDatatype.sum cF dF, Nat.succ k, c, hnth, hWf => by
      have hnth' : dt_nth_cons dF k = some c := by
        simpa [dt_nth_cons] using hnth
      simp only [__smtx_dt_wf_rec, native_and, Bool.and_eq_true] at hWf
      exact dt_wf_nth_cons dd dF k c hnth' hWf.2

theorem resolved_field_inh_wf
    (dd : SmtDatatypeDecl) (hDecl : __smtx_decl_wf_rec dd dd = true) :
    ∀ (c : SmtDatatypeCons), __smtx_dt_cons_wf_rec dd c = true ->
      ∀ F ∈ dtc_fields c,
        native_inhabited_type (resolve_ty dd F) = true ∧
          __smtx_type_wf_rec (resolve_ty dd F) = true
  | SmtDatatypeCons.unit, _, F, hF => by
      simp [dtc_fields] at hF
  | SmtDatatypeCons.cons T c, hWf, F, hF => by
      have hF' : F = T ∨ F ∈ dtc_fields c := by
        simpa [dtc_fields] using hF
      rcases hF' with hFT | hFc
      · subst F
        cases T with
        | TypeRef t =>
            have hParts :
                __smtx_dd_has_dt t dd = true ∧
                  __smtx_dt_cons_wf_rec dd c = true := by
              simpa [__smtx_dt_cons_wf_rec, native_and] using hWf
            refine ⟨decl_wf_rec_inh t dd dd hParts.1 hDecl, ?_⟩
            simp [resolve_ty, __smtx_type_wf_rec, native_and, hParts.1, hDecl]
        | Bool =>
            have hParts := hWf
            simp [__smtx_dt_cons_wf_rec, native_and] at hParts
            exact ⟨hParts.1.1, hParts.1.2⟩
        | Int =>
            have hParts := hWf
            simp [__smtx_dt_cons_wf_rec, native_and] at hParts
            exact ⟨hParts.1.1, hParts.1.2⟩
        | Real =>
            have hParts := hWf
            simp [__smtx_dt_cons_wf_rec, native_and] at hParts
            exact ⟨hParts.1.1, hParts.1.2⟩
        | RegLan =>
            have hParts := hWf
            simp [__smtx_dt_cons_wf_rec, native_and] at hParts
            exact ⟨hParts.1.1, hParts.1.2⟩
        | BitVec w =>
            have hParts := hWf
            simp [__smtx_dt_cons_wf_rec, native_and] at hParts
            exact ⟨hParts.1.1, hParts.1.2⟩
        | Char =>
            have hParts := hWf
            simp [__smtx_dt_cons_wf_rec, native_and] at hParts
            exact ⟨hParts.1.1, hParts.1.2⟩
        | Map T2 U2 =>
            have hParts := hWf
            simp [__smtx_dt_cons_wf_rec, native_and] at hParts
            exact ⟨hParts.1.1, hParts.1.2⟩
        | Set T2 =>
            have hParts := hWf
            simp [__smtx_dt_cons_wf_rec, native_and] at hParts
            exact ⟨hParts.1.1, hParts.1.2⟩
        | Seq T2 =>
            have hParts := hWf
            simp [__smtx_dt_cons_wf_rec, native_and] at hParts
            exact ⟨hParts.1.1, hParts.1.2⟩
        | USort i =>
            have hParts := hWf
            simp [__smtx_dt_cons_wf_rec, native_and] at hParts
            exact ⟨hParts.1.1, hParts.1.2⟩
        | FunType T2 U2 =>
            have hParts := hWf
            simp [__smtx_dt_cons_wf_rec, native_and] at hParts
            exact ⟨hParts.1.1, hParts.1.2⟩
        | DtcAppType T2 U2 =>
            have hParts := hWf
            simp [__smtx_dt_cons_wf_rec, native_and] at hParts
            exact ⟨hParts.1.1, hParts.1.2⟩
        | Datatype s2 dd2 =>
            have hParts := hWf
            simp [__smtx_dt_cons_wf_rec, native_and] at hParts
            exact ⟨hParts.1.1, hParts.1.2⟩
        | None =>
            have hParts := hWf
            simp [__smtx_dt_cons_wf_rec, native_and] at hParts
            exact ⟨hParts.1.1, hParts.1.2⟩
      · have hTail : __smtx_dt_cons_wf_rec dd c = true := by
          cases T <;>
            simp [__smtx_dt_cons_wf_rec, native_and] at hWf <;>
              first
                | exact hWf.2
                | exact hWf.2.2
        exact resolved_field_inh_wf dd hDecl c hTail F hFc

/-- The finiteness fixpoint of a declaration. -/
def bounded_fix (dd : SmtDatatypeDecl) : SmtDatatypeDecl :=
  __smtx_datatype_decl_bounded false dd dd SmtDatatypeDecl.nil

theorem is_finite_datatype_eq (s : native_String) (dd : SmtDatatypeDecl) :
    __smtx_is_finite_type (SmtType.Datatype s dd) =
      __smtx_dd_has_dt s (bounded_fix dd) := by
  simp [__smtx_is_finite_type, __smtx_type_bounded, bounded_fix]

private theorem unbounded_field_infinite
    (dd : SmtDatatypeDecl) (F : SmtType)
    (hUnb : __smtx_field_type_bounded false F (bounded_fix dd) = false) :
    __smtx_is_finite_type (resolve_ty dd F) = false := by
  cases F <;>
    simp [__smtx_field_type_bounded, resolve_ty, __smtx_is_finite_type,
      __smtx_type_bounded, bounded_fix] at hUnb ⊢ <;>
    exact hUnb

-- === the constructor type chain ===

def dtc_chain_type (Bt : SmtType) : List SmtType -> SmtType
  | [] => Bt
  | U :: Us => SmtType.DtcAppType U (dtc_chain_type Bt Us)

theorem typeof_dt_cons_value_rec_chain_zero (T : SmtType) :
    ∀ (c : SmtDatatypeCons) (d : SmtDatatype),
      __smtx_typeof_dt_cons_value_rec T (SmtDatatype.sum c d) 0 =
        dtc_chain_type T (dtc_fields c)
  | SmtDatatypeCons.unit, d => by
      simp [__smtx_typeof_dt_cons_value_rec, dtc_fields, dtc_chain_type]
  | SmtDatatypeCons.cons U c, d => by
      simp [__smtx_typeof_dt_cons_value_rec, dtc_fields, dtc_chain_type,
        typeof_dt_cons_value_rec_chain_zero T c d]

theorem typeof_dt_cons_value_rec_nth (T : SmtType) :
    ∀ (d : SmtDatatype) (k : Nat) (c : SmtDatatypeCons),
      dt_nth_cons d k = some c ->
        __smtx_typeof_dt_cons_value_rec T d k =
          dtc_chain_type T (dtc_fields c)
  | SmtDatatype.null, k, c, hnth => by
      simp [dt_nth_cons] at hnth
  | SmtDatatype.sum cF dF, 0, c, hnth => by
      have hc : cF = c := by simpa [dt_nth_cons] using hnth
      subst c
      exact typeof_dt_cons_value_rec_chain_zero T cF dF
  | SmtDatatype.sum cF dF, Nat.succ k, c, hnth => by
      have hnth' : dt_nth_cons dF k = some c := by
        simpa [dt_nth_cons] using hnth
      simpa [__smtx_typeof_dt_cons_value_rec] using
        typeof_dt_cons_value_rec_nth T dF k c hnth'

theorem dt_resolve_nth (dd : SmtDatatypeDecl) :
    ∀ (d : SmtDatatype) (k : Nat) (c : SmtDatatypeCons),
      dt_nth_cons d k = some c ->
        dt_nth_cons (__smtx_dt_resolve d dd) k =
          some (__smtx_dtc_resolve c dd)
  | SmtDatatype.null, k, c, hnth => by
      simp [dt_nth_cons] at hnth
  | SmtDatatype.sum cF dF, 0, c, hnth => by
      have hc : cF = c := by simpa [dt_nth_cons] using hnth
      subst c
      simp [__smtx_dt_resolve, dt_nth_cons]
  | SmtDatatype.sum cF dF, Nat.succ k, c, hnth => by
      have hnth' : dt_nth_cons dF k = some c := by
        simpa [dt_nth_cons] using hnth
      simpa [__smtx_dt_resolve, dt_nth_cons] using
        dt_resolve_nth dd dF k c hnth'

-- === spines ===

def build_spine : SmtValue -> List SmtValue -> SmtValue
  | f, [] => f
  | f, v :: vs => build_spine (SmtValue.Apply f v) vs

def list_typed_canonical : List SmtValue -> List SmtType -> Prop
  | [], [] => True
  | v :: vs, U :: Us =>
      (__smtx_typeof_value v = U ∧ U ≠ SmtType.None ∧
        __smtx_value_canonical v = true) ∧ list_typed_canonical vs Us
  | _, _ => False

theorem build_spine_typeof (Bt : SmtType) :
    ∀ (Us : List SmtType) (vs : List SmtValue) (f : SmtValue),
      __smtx_typeof_value f = dtc_chain_type Bt Us ->
      list_typed_canonical vs Us ->
      __smtx_typeof_value (build_spine f vs) = Bt
  | [], [], f, hTy, _ => by
      simpa [build_spine, dtc_chain_type] using hTy
  | [], v :: vs, f, _, hTyped => by
      simp [list_typed_canonical] at hTyped
  | U :: Us, [], f, _, hTyped => by
      simp [list_typed_canonical] at hTyped
  | U :: Us, v :: vs, f, hTy, hTyped => by
      have hParts := hTyped
      simp only [list_typed_canonical] at hParts
      have hUNone : native_Teq U SmtType.None = false := by
        simp [native_Teq, hParts.1.2.1]
      have hStep :
          __smtx_typeof_value (SmtValue.Apply f v) = dtc_chain_type Bt Us := by
        simp [__smtx_typeof_value, hTy, dtc_chain_type,
          __smtx_typeof_apply_value, __smtx_typeof_guard, hParts.1.1,
          native_ite, native_Teq, hUNone, hParts.1.2.1]
      simpa [build_spine] using
        build_spine_typeof Bt Us vs (SmtValue.Apply f v) hStep hParts.2

theorem build_spine_canonical :
    ∀ (Us : List SmtType) (vs : List SmtValue) (f : SmtValue),
      __smtx_value_canonical f = true ->
      list_typed_canonical vs Us ->
      __smtx_value_canonical (build_spine f vs) = true
  | [], [], f, hCan, _ => by
      simpa [build_spine] using hCan
  | [], v :: vs, f, _, hTyped => by
      simp [list_typed_canonical] at hTyped
  | U :: Us, [], f, _, hTyped => by
      simp [list_typed_canonical] at hTyped
  | U :: Us, v :: vs, f, hCan, hTyped => by
      have hParts := hTyped
      simp only [list_typed_canonical] at hParts
      have hApplyCan :
          __smtx_value_canonical (SmtValue.Apply f v) = true := by
        simp [__smtx_value_canonical, native_and, hCan, hParts.1.2.2]
      simpa [build_spine] using
        build_spine_canonical Us vs (SmtValue.Apply f v) hApplyCan hParts.2

theorem build_spine_size_ge_head :
    ∀ (vs : List SmtValue) (f : SmtValue),
      sizeOf f ≤ sizeOf (build_spine f vs)
  | [], f => by
      simp [build_spine]
  | v :: vs, f => by
      have hRec := build_spine_size_ge_head vs (SmtValue.Apply f v)
      have hApply : sizeOf f ≤ sizeOf (SmtValue.Apply f v) := by
        rw [show sizeOf (SmtValue.Apply f v) = 1 + sizeOf f + sizeOf v by rfl]
        omega
      simpa [build_spine] using Nat.le_trans hApply hRec

theorem build_spine_size_ge_mem :
    ∀ (vs : List SmtValue) (f : SmtValue) (v : SmtValue),
      v ∈ vs ->
        sizeOf v + 1 ≤ sizeOf (build_spine f vs)
  | [], f, v, hv => by
      cases hv
  | w :: vs, f, v, hv => by
      rcases List.mem_cons.mp hv with hEq | hTail
      · subst v
        have hHead := build_spine_size_ge_head vs (SmtValue.Apply f w)
        have hApply : sizeOf w + 1 ≤ sizeOf (SmtValue.Apply f w) := by
          rw [show sizeOf (SmtValue.Apply f w) = 1 + sizeOf f + sizeOf w by rfl]
          omega
        simpa [build_spine] using Nat.le_trans hApply hHead
      · simpa [build_spine] using
          build_spine_size_ge_mem vs (SmtValue.Apply f w) v hTail

-- === default field values ===

def defaults_of : List SmtType -> List SmtValue
  | [] => []
  | U :: Us => __smtx_type_default U :: defaults_of Us

theorem list_typed_canonical_defaults :
    ∀ Us : List SmtType,
      (∀ U ∈ Us,
        native_inhabited_type U = true ∧ __smtx_type_wf_rec U = true) ->
      list_typed_canonical (defaults_of Us) Us
  | [], _ => by
      simp [defaults_of, list_typed_canonical]
  | U :: Us, hWf => by
      have hU := hWf U (by simp)
      have hKernel := type_default_kernel U hU.1 hU.2
      have hNone : U ≠ SmtType.None := by
        intro hEq
        subst U
        simp [native_inhabited_type, native_Teq, native_not, native_and] at hU
      refine ⟨⟨hKernel.1, hNone, hKernel.2⟩, ?_⟩
      exact list_typed_canonical_defaults Us (fun V hV => hWf V (by simp [hV]))

theorem list_typed_canonical_append :
    ∀ {vs1 : List SmtValue} {Us1 : List SmtType}
      {vs2 : List SmtValue} {Us2 : List SmtType},
      list_typed_canonical vs1 Us1 ->
      list_typed_canonical vs2 Us2 ->
      list_typed_canonical (vs1 ++ vs2) (Us1 ++ Us2)
  | [], [], vs2, Us2, _, h2 => by
      simpa using h2
  | [], U :: Us, vs2, Us2, h1, _ => by
      simp [list_typed_canonical] at h1
  | v :: vs, [], vs2, Us2, h1, _ => by
      simp [list_typed_canonical] at h1
  | v :: vs, U :: Us, vs2, Us2, h1, h2 => by
      have hParts := h1
      simp only [list_typed_canonical] at hParts
      exact ⟨hParts.1, list_typed_canonical_append hParts.2 h2⟩

/-!
## Part C: the unbounded constructor of an infinite datatype
-/

theorem veq_eq_of_true {a b : SmtValue}
    (h : native_veq a b = true) : a = b := by
  simpa [native_veq] using h

theorem veq_refl_true (a : SmtValue) : native_veq a a = true := by
  simp [native_veq]

private theorem type_default_typed_canonical_p
    {T : SmtType}
    (hInh : native_inhabited_type T = true)
    (hRec : __smtx_type_wf_rec T = true) :
    __smtx_typeof_value (__smtx_type_default T) = T ∧
      __smtx_value_canonical (__smtx_type_default T) = true :=
  type_default_kernel T hInh hRec

theorem ne_none_of_inh {T : SmtType}
    (h : native_inhabited_type T = true) : T ≠ SmtType.None := by
  intro hN
  subst T
  simp [native_inhabited_type, native_Teq, native_not, native_and] at h

theorem default_ne_notValue_of_inh {T : SmtType}
    (hInh : native_inhabited_type T = true) :
    __smtx_type_default T ≠ SmtValue.NotValue := by
  intro hEq
  have hTy := type_default_typed_of_inhabited T hInh
  rw [hEq] at hTy
  simp [__smtx_typeof_value] at hTy
  exact ne_none_of_inh hInh hTy.symm

/--
An infinite well-formed datatype has a constructor whose fields are all
inhabited and well-formed, with at least one field of infinite type.  The
constructor's value-level type is the corresponding `DtcAppType` chain over
the resolved field types.
-/
private theorem infinite_datatype_unbounded_constructor
    (s : native_String) (dd : SmtDatatypeDecl)
    (hRec : __smtx_type_wf_rec (SmtType.Datatype s dd) = true)
    (hInfinite : __smtx_is_finite_type (SmtType.Datatype s dd) = false) :
    ∃ (k : Nat) (preU postU : List SmtType) (X : SmtType),
      __smtx_typeof_value (SmtValue.DtCons s dd k) =
        dtc_chain_type (SmtType.Datatype s dd) (preU ++ X :: postU) ∧
      (∀ U ∈ preU ++ X :: postU,
        native_inhabited_type U = true ∧ __smtx_type_wf_rec U = true) ∧
      __smtx_is_finite_type X = false := by
  have hRecParts :
      __smtx_dd_has_dt s dd = true ∧ __smtx_decl_wf_rec dd dd = true := by
    simpa [__smtx_type_wf_rec, native_and] using hRec
  have hNotFix : __smtx_dd_has_dt s (bounded_fix dd) = false := by
    rw [is_finite_datatype_eq] at hInfinite
    exact hInfinite
  have hUnbLookup :
      __smtx_datatype_bounded false (__smtx_dd_lookup s dd)
        (bounded_fix dd) = false :=
    unbounded_lookup_of_not_fix false dd s hRecParts.1 hNotFix
  have hDtWf : __smtx_dt_wf_rec dd (__smtx_dd_lookup s dd) = true :=
    decl_wf_rec_lookup_local s dd dd hRecParts.1 hRecParts.2
  rcases unbounded_datatype_has_unbounded_cons
      (__smtx_dd_lookup s dd) hUnbLookup with ⟨k, c, hnth, hConsUnb⟩
  have hConsWf : __smtx_dt_cons_wf_rec dd c = true :=
    dt_wf_nth_cons dd (__smtx_dd_lookup s dd) k c hnth hDtWf
  rcases unbounded_cons_has_unbounded_field c hConsUnb with
    ⟨pre, F, post, hFields, hFieldUnb⟩
  refine
    ⟨k, pre.map (resolve_ty dd), post.map (resolve_ty dd), resolve_ty dd F,
      ?_, ?_, ?_⟩
  · have hTy :
        __smtx_typeof_value (SmtValue.DtCons s dd k) =
          __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s dd)
            (__smtx_dt_resolve (__smtx_dd_lookup s dd) dd) k := by
      simp [__smtx_typeof_value]
    rw [hTy,
      typeof_dt_cons_value_rec_nth (SmtType.Datatype s dd)
        (__smtx_dt_resolve (__smtx_dd_lookup s dd) dd) k
        (__smtx_dtc_resolve c dd)
        (dt_resolve_nth dd (__smtx_dd_lookup s dd) k c hnth),
      dtc_resolve_fields dd c, hFields]
    simp
  · intro U hU
    have hUmem : U ∈ (dtc_fields c).map (resolve_ty dd) := by
      rw [hFields]
      simpa using hU
    rcases List.mem_map.mp hUmem with ⟨F', hF'mem, hF'eq⟩
    rw [← hF'eq]
    exact resolved_field_inh_wf dd hRecParts.2 c hConsWf F' hF'mem
  · exact unbounded_field_infinite dd F hFieldUnb

/-!
## Part D: the fuel-indexed pump

`LargeOracle n` supplies typed canonical values of size at least `n` for
every infinite well-formed inhabited datatype.  The successor step picks the
unbounded constructor, fills the designated infinite field with a large value
of the previous level (`type_large` handles ground field types structurally),
and pads the remaining fields with defaults.
-/

private def LargeOracle (n : Nat) : Prop :=
  ∀ (s : native_String) (dd : SmtDatatypeDecl),
    native_inhabited_type (SmtType.Datatype s dd) = true →
    __smtx_type_wf_rec (SmtType.Datatype s dd) = true →
    __smtx_is_finite_type (SmtType.Datatype s dd) = false →
    ∃ v : SmtValue,
      __smtx_typeof_value v = SmtType.Datatype s dd ∧
        __smtx_value_canonical v = true ∧ n ≤ sizeOf v

-- === finiteness/unit unfolding on containers (local copies) ===

private theorem is_finite_map_eq_p (T U : SmtType) :
    __smtx_is_finite_type (SmtType.Map T U) =
      native_or (__smtx_is_unit_type U)
        (native_and (__smtx_is_finite_type T) (__smtx_is_finite_type U)) := by
  simp [__smtx_is_finite_type, __smtx_is_unit_type, __smtx_type_bounded,
    native_and, native_not]

private theorem is_finite_set_eq_p (T : SmtType) :
    __smtx_is_finite_type (SmtType.Set T) = __smtx_is_finite_type T := by
  simp [__smtx_is_finite_type, __smtx_type_bounded, native_and, native_not]

private theorem is_unit_map_eq_p (T U : SmtType) :
    __smtx_is_unit_type (SmtType.Map T U) = __smtx_is_unit_type U := by
  simp [__smtx_is_unit_type, __smtx_type_bounded, native_or, native_and,
    native_not]

private theorem is_unit_bitvec_eq_p (w : Nat) :
    __smtx_is_unit_type (SmtType.BitVec w) = native_nateq w 0 := by
  simp [__smtx_is_unit_type, __smtx_type_bounded, native_or, native_not,
    native_nateq]

-- === large ground witnesses ===

private theorem int_large_witness_p (minSize : Nat) :
    ∃ i : SmtValue,
      __smtx_typeof_value i = SmtType.Int ∧
        __smtx_value_canonical i = true ∧
          minSize ≤ sizeOf i := by
  refine ⟨SmtValue.Numeral (Int.ofNat minSize), ?_, ?_, ?_⟩
  · simp [__smtx_typeof_value]
  · simp [__smtx_value_canonical]
  · rw [show sizeOf (SmtValue.Numeral (Int.ofNat minSize)) =
        1 + sizeOf (Int.ofNat minSize) by rfl]
    rw [show sizeOf (Int.ofNat minSize) = 1 + minSize by rfl]
    omega

private theorem real_large_witness_p (minSize : Nat) :
    ∃ i : SmtValue,
      __smtx_typeof_value i = SmtType.Real ∧
        __smtx_value_canonical i = true ∧
          minSize ≤ sizeOf i := by
  refine ⟨SmtValue.Rational (Int.ofNat minSize : native_Rat), ?_, ?_, ?_⟩
  · simp [__smtx_typeof_value]
  · simp [__smtx_value_canonical]
  · rw [show sizeOf (SmtValue.Rational (Int.ofNat minSize : native_Rat)) =
        1 + sizeOf (Int.ofNat minSize : native_Rat) by rfl]
    rw [show sizeOf (Int.ofNat minSize : native_Rat) =
        1 + sizeOf (Int.ofNat minSize) + sizeOf (1 : Nat) +
          sizeOf (by decide : (1 : Nat) ≠ 0) by rfl]
    rw [show sizeOf (Int.ofNat minSize) = 1 + minSize by rfl]
    omega

private theorem usort_large_witness_p (u : native_Nat) (minSize : Nat) :
    ∃ i : SmtValue,
      __smtx_typeof_value i = SmtType.USort u ∧
        __smtx_value_canonical i = true ∧
          minSize ≤ sizeOf i := by
  refine ⟨SmtValue.UValue u minSize, ?_, ?_, ?_⟩
  · simp [__smtx_typeof_value]
  · simp [__smtx_value_canonical]
  · rw [show sizeOf (SmtValue.UValue u minSize) =
        1 + sizeOf u + sizeOf minSize by rfl]
    simp [sizeOf]

-- === large seq witnesses ===

private def smt_seq_repeat_p (T : SmtType) (x : SmtValue) : Nat -> SmtSeq
  | 0 => SmtSeq.empty T
  | Nat.succ n => SmtSeq.cons x (smt_seq_repeat_p T x n)

private theorem smt_seq_repeat_typeof_p
    (T : SmtType) (x : SmtValue) (hx : __smtx_typeof_value x = T) :
    ∀ n : Nat,
      __smtx_typeof_seq_value (smt_seq_repeat_p T x n) = SmtType.Seq T
  | 0 => by
      simp [smt_seq_repeat_p, __smtx_typeof_seq_value]
  | Nat.succ n => by
      simp [smt_seq_repeat_p, __smtx_typeof_seq_value,
        smt_seq_repeat_typeof_p T x hx n, hx, native_ite, native_Teq]

private theorem smt_seq_repeat_canonical_p
    (T : SmtType) (x : SmtValue) (hx : __smtx_value_canonical x = true) :
    ∀ n : Nat,
      __smtx_seq_canonical (smt_seq_repeat_p T x n) = true
  | 0 => by
      simp [smt_seq_repeat_p, __smtx_seq_canonical]
  | Nat.succ n => by
      simp [smt_seq_repeat_p, __smtx_seq_canonical, native_and, hx,
        smt_seq_repeat_canonical_p T x hx n]

private theorem smt_seq_repeat_size_ge_p
    (T : SmtType) (x : SmtValue) :
    ∀ n : Nat, n ≤ sizeOf (smt_seq_repeat_p T x n)
  | 0 => Nat.zero_le _
  | Nat.succ n => by
      have hRec := smt_seq_repeat_size_ge_p T x n
      rw [show smt_seq_repeat_p T x (Nat.succ n) =
        SmtSeq.cons x (smt_seq_repeat_p T x n) by rfl]
      rw [show sizeOf (SmtSeq.cons x (smt_seq_repeat_p T x n)) =
        1 + sizeOf x + sizeOf (smt_seq_repeat_p T x n) by rfl]
      omega

private theorem seq_large_witness_p
    (T : SmtType)
    (hInh : native_inhabited_type T = true)
    (hRec : __smtx_type_wf_rec T = true)
    (minSize : Nat) :
    ∃ i : SmtValue,
      __smtx_typeof_value i = SmtType.Seq T ∧
        __smtx_value_canonical i = true ∧
          minSize ≤ sizeOf i := by
  have hDef := type_default_typed_canonical_p hInh hRec
  refine
    ⟨SmtValue.Seq (smt_seq_repeat_p T (__smtx_type_default T) minSize),
      ?_, ?_, ?_⟩
  · simpa [__smtx_typeof_value] using
      smt_seq_repeat_typeof_p T (__smtx_type_default T) hDef.1 minSize
  · simpa [__smtx_value_canonical] using
      smt_seq_repeat_canonical_p T (__smtx_type_default T) hDef.2 minSize
  · rw [show
      sizeOf
          (SmtValue.Seq (smt_seq_repeat_p T (__smtx_type_default T) minSize)) =
        1 + sizeOf (smt_seq_repeat_p T (__smtx_type_default T) minSize) by rfl]
    have := smt_seq_repeat_size_ge_p T (__smtx_type_default T) minSize
    omega

-- === bitvec witnesses (local copies) ===

private theorem one_mod_pow2_succ_p (w : Nat) :
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

private theorem one_mod_pow2_succ_zeq_p (w : Nat) :
    native_zeq (1 : Int)
      (native_mod_total 1 (native_int_pow2 (native_nat_to_int (Nat.succ w)))) = true := by
  simp [native_zeq, native_mod_total, one_mod_pow2_succ_p]

private theorem bitvec_succ_nonneg_p (w : Nat) :
    native_zleq 0 (native_nat_to_int (Nat.succ w)) = true := by
  exact decide_eq_true (Int.natCast_nonneg (Nat.succ w))

private theorem bitvec_succ_one_typeof_p (w : Nat) :
    __smtx_typeof_value
      (SmtValue.Binary (native_nat_to_int (Nat.succ w)) 1) =
        SmtType.BitVec (Nat.succ w) := by
  have hmod := one_mod_pow2_succ_zeq_p w
  have hnonneg := bitvec_succ_nonneg_p w
  have htonat : native_int_to_nat (native_nat_to_int (Nat.succ w)) = Nat.succ w := by
    simp [native_int_to_nat, native_nat_to_int]
  simp [__smtx_typeof_value, native_and, native_ite, hmod, hnonneg, htonat]

private theorem bitvec_succ_one_canonical_p (w : Nat) :
    __smtx_value_canonical
      (SmtValue.Binary (native_nat_to_int (Nat.succ w)) 1) = true := by
  have hmod := one_mod_pow2_succ_zeq_p w
  have hnonneg := bitvec_succ_nonneg_p w
  simp [__smtx_value_canonical, native_ite, hmod, hnonneg]

private theorem bitvec_succ_one_ne_default_p (w : Nat) :
    native_veq
      (SmtValue.Binary (native_nat_to_int (Nat.succ w)) 1)
      (__smtx_type_default (SmtType.BitVec (Nat.succ w))) = false := by
  simp [__smtx_type_default, native_nat_to_int, native_veq]

/-!
## Part E: infrastructure for the finite non-unit witness

Suffix structure of declarations, name uniqueness from well-formedness,
positive soundness of the finiteness fixpoint, the spine form of generated
defaults, and spine injectivity.
-/

inductive SuffixOf : SmtDatatypeDecl -> SmtDatatypeDecl -> Prop where
  | refl (dd : SmtDatatypeDecl) : SuffixOf dd dd
  | tail (s : native_String) (d : SmtDatatype) {ddS dd : SmtDatatypeDecl} :
      SuffixOf ddS dd -> SuffixOf ddS (SmtDatatypeDecl.cons s d dd)

theorem suffixOf_cons_inner {sF : native_String} {dF : SmtDatatype}
    {rest : SmtDatatypeDecl} :
    ∀ {dd : SmtDatatypeDecl},
      SuffixOf (SmtDatatypeDecl.cons sF dF rest) dd ->
        SuffixOf rest dd
  | SmtDatatypeDecl.nil, h => by
      cases h
  | SmtDatatypeDecl.cons s1 d1 dd1, h => by
      cases h with
      | refl => exact SuffixOf.tail sF dF (SuffixOf.refl rest)
      | tail _ _ h' => exact SuffixOf.tail s1 d1 (suffixOf_cons_inner h')

theorem suffixOf_has_dt {t : native_String} {ddS : SmtDatatypeDecl} :
    ∀ {dd : SmtDatatypeDecl},
      SuffixOf ddS dd ->
      __smtx_dd_has_dt t ddS = true ->
        __smtx_dd_has_dt t dd = true
  | SmtDatatypeDecl.nil, hSuf, hMem => by
      cases hSuf
      exact hMem
  | SmtDatatypeDecl.cons s1 d1 dd1, hSuf, hMem => by
      cases hSuf with
      | refl => exact hMem
      | tail _ _ h' =>
          have := suffixOf_has_dt h' hMem
          simp [__smtx_dd_has_dt, native_or, this]

/-- Name uniqueness of a declaration, as recorded by `__smtx_decl_wf_rec`. -/
def dd_unique : SmtDatatypeDecl -> Prop
  | SmtDatatypeDecl.nil => True
  | SmtDatatypeDecl.cons s _ rest =>
      __smtx_dd_has_dt s rest = false ∧ dd_unique rest

theorem dd_unique_of_decl_wf (dd : SmtDatatypeDecl) :
    ∀ dd2 : SmtDatatypeDecl,
      __smtx_decl_wf_rec dd dd2 = true -> dd_unique dd2
  | SmtDatatypeDecl.nil, _ => trivial
  | SmtDatatypeDecl.cons s d rest, h => by
      simp only [__smtx_decl_wf_rec, native_and, native_not,
        Bool.and_eq_true] at h
      refine ⟨?_, dd_unique_of_decl_wf dd rest h.2.2.1⟩
      have hNot := h.2.2.2
      cases hHas : __smtx_dd_has_dt s rest
      · rfl
      · rw [hHas] at hNot
        cases hNot

/-- In a duplicate-free declaration, lookup lands on a suffix's head entry. -/
theorem suffix_head_lookup {sF : native_String} {dF : SmtDatatype}
    {rest : SmtDatatypeDecl} :
    ∀ {dd : SmtDatatypeDecl},
      SuffixOf (SmtDatatypeDecl.cons sF dF rest) dd ->
      dd_unique dd ->
      __smtx_dd_lookup sF dd = dF
  | SmtDatatypeDecl.nil, hSuf, _ => by
      cases hSuf
  | SmtDatatypeDecl.cons s1 d1 dd1, hSuf, hUniq => by
      cases hSuf with
      | refl =>
          simp [__smtx_dd_lookup, native_ite, native_streq]
      | tail _ _ h' =>
          have hMemInner : __smtx_dd_has_dt sF dd1 = true :=
            suffixOf_has_dt h'
              (by simp [__smtx_dd_has_dt, native_or, native_streq])
          have hParts : __smtx_dd_has_dt s1 dd1 = false ∧ dd_unique dd1 := by
            simpa [dd_unique] using hUniq
          by_cases hs : native_streq sF s1 = true
          · have hEq : sF = s1 := by simpa [native_streq] using hs
            subst s1
            rw [hParts.1] at hMemInner
            cases hMemInner
          · have := suffix_head_lookup h' hParts.2
            simpa [__smtx_dd_lookup, native_ite, hs] using this

/--
A successful suffix-scan default agrees with the full-declaration default in
a duplicate-free declaration.
-/
theorem suffix_decl_default_eq
    (t : native_String) (dd : SmtDatatypeDecl) :
    ∀ {ddS dd2 : SmtDatatypeDecl},
      SuffixOf ddS dd2 ->
      dd_unique dd2 ->
      __smtx_dd_has_dt t ddS = true ->
      __smtx_datatype_decl_default t dd ddS =
        __smtx_datatype_decl_default t dd dd2
  | ddS, SmtDatatypeDecl.nil, hSuf, _, hMem => by
      cases hSuf
      simp [__smtx_dd_has_dt] at hMem
  | ddS, SmtDatatypeDecl.cons s1 d1 dd1, hSuf, hUniq, hMem => by
      cases hSuf with
      | refl => rfl
      | tail _ _ h' =>
          have hMemOuter : __smtx_dd_has_dt t dd1 = true :=
            suffixOf_has_dt h' hMem
          have hParts : __smtx_dd_has_dt s1 dd1 = false ∧ dd_unique dd1 := by
            simpa [dd_unique] using hUniq
          by_cases hs : native_streq t s1 = true
          · have hEq : t = s1 := by simpa [native_streq] using hs
            subst s1
            rw [hParts.1] at hMemOuter
            cases hMemOuter
          · rw [suffix_decl_default_eq t dd h' hParts.2 hMem]
            simp [__smtx_datatype_decl_default, native_ite, hs]

theorem decl_default_has_dt_of_ne_notValue
    (t : native_String) (dd : SmtDatatypeDecl) :
    ∀ ddS : SmtDatatypeDecl,
      __smtx_datatype_decl_default t dd ddS ≠ SmtValue.NotValue ->
        __smtx_dd_has_dt t ddS = true
  | SmtDatatypeDecl.nil, h => by
      simp [__smtx_datatype_decl_default] at h
  | SmtDatatypeDecl.cons sF dF rest, h => by
      by_cases hs : native_streq t sF = true
      · simp [__smtx_dd_has_dt, native_or, hs]
      · simp only [__smtx_datatype_decl_default, native_ite, hs,
          if_neg] at h
        have := decl_default_has_dt_of_ne_notValue t dd rest (by
          intro hEq
          exact h (by simpa [native_ite, hs] using hEq))
        simp [__smtx_dd_has_dt, native_or, hs, this]

/-- The default of a name whose body is empty fails. -/
theorem decl_default_of_lookup_null
    (t : native_String) (dd : SmtDatatypeDecl) :
    ∀ ddS : SmtDatatypeDecl,
      __smtx_dd_lookup t ddS = SmtDatatype.null ->
        __smtx_datatype_decl_default t dd ddS = SmtValue.NotValue
  | SmtDatatypeDecl.nil, _ => by
      simp [__smtx_datatype_decl_default]
  | SmtDatatypeDecl.cons sF dF rest, hLk => by
      by_cases hs : native_streq t sF = true
      · have hdF : dF = SmtDatatype.null := by
          simpa [__smtx_dd_lookup, native_ite, hs] using hLk
        subst dF
        simp [__smtx_datatype_decl_default, native_ite, hs,
          __smtx_datatype_default]
      · have hLk' : __smtx_dd_lookup t rest = SmtDatatype.null := by
          simpa [__smtx_dd_lookup, native_ite, hs] using hLk
        simpa [__smtx_datatype_decl_default, native_ite, hs] using
          decl_default_of_lookup_null t dd rest hLk'

/-- The scan structure of the full-declaration default. -/
theorem decl_default_find
    (t : native_String) (dd : SmtDatatypeDecl) :
    ∀ ddS : SmtDatatypeDecl,
      __smtx_dd_has_dt t ddS = true ->
        ∃ ddTail : SmtDatatypeDecl,
          SuffixOf (SmtDatatypeDecl.cons t (__smtx_dd_lookup t ddS) ddTail) ddS ∧
          __smtx_datatype_decl_default t dd ddS =
            __smtx_datatype_default t dd 0 (__smtx_dd_lookup t ddS) ddTail
  | SmtDatatypeDecl.nil, hMem => by
      simp [__smtx_dd_has_dt] at hMem
  | SmtDatatypeDecl.cons sF dF rest, hMem => by
      by_cases hs : native_streq t sF = true
      · have hEq : t = sF := by simpa [native_streq] using hs
        subst sF
        refine ⟨rest, ?_, ?_⟩
        · have hLk : __smtx_dd_lookup t (SmtDatatypeDecl.cons t dF rest) = dF := by
            simp [__smtx_dd_lookup, native_ite, native_streq]
          rw [hLk]
          exact SuffixOf.refl _
        · simp [__smtx_datatype_decl_default, __smtx_dd_lookup, native_ite,
            native_streq]
      · have hMem' : __smtx_dd_has_dt t rest = true := by
          simpa [__smtx_dd_has_dt, native_or, hs] using hMem
        rcases decl_default_find t dd rest hMem' with ⟨ddTail, hSuf, hEq⟩
        refine ⟨ddTail, ?_, ?_⟩
        · have hLk :
              __smtx_dd_lookup t (SmtDatatypeDecl.cons sF dF rest) =
                __smtx_dd_lookup t rest := by
            simp [__smtx_dd_lookup, native_ite, hs]
          rw [hLk]
          exact SuffixOf.tail sF dF hSuf
        · simpa [__smtx_datatype_decl_default, __smtx_dd_lookup, native_ite,
            hs] using hEq

-- === positive soundness of the fixpoint ===

theorem bounded_cons_field {u : native_Bool} {B : SmtDatatypeDecl} :
    ∀ c : SmtDatatypeCons,
      __smtx_datatype_cons_bounded u c B = true ->
        ∀ F ∈ dtc_fields c, __smtx_field_type_bounded u F B = true
  | SmtDatatypeCons.unit, _, F, hF => by
      simp [dtc_fields] at hF
  | SmtDatatypeCons.cons T c, h, F, hF => by
      simp only [__smtx_datatype_cons_bounded, native_and,
        Bool.and_eq_true] at h
      have hF' : F = T ∨ F ∈ dtc_fields c := by
        simpa [dtc_fields] using hF
      rcases hF' with hFT | hFc
      · subst F
        exact h.1
      · exact bounded_cons_field c h.2 F hFc

theorem bounded_datatype_cons {u : native_Bool} {B : SmtDatatypeDecl} :
    ∀ (d : SmtDatatype) (k : Nat) (c : SmtDatatypeCons),
      dt_nth_cons d k = some c ->
        __smtx_datatype_bounded u d B = true ->
        __smtx_datatype_cons_bounded u c B = true
  | SmtDatatype.null, k, c, hnth, _ => by
      simp [dt_nth_cons] at hnth
  | SmtDatatype.sum cF SmtDatatype.null, 0, c, hnth, hBnd => by
      have hc : cF = c := by simpa [dt_nth_cons] using hnth
      subst c
      simpa [__smtx_datatype_bounded] using hBnd
  | SmtDatatype.sum cF SmtDatatype.null, Nat.succ k, c, hnth, _ => by
      simp [dt_nth_cons] at hnth
  | SmtDatatype.sum cF (SmtDatatype.sum c2 d2), 0, c, hnth, hBnd => by
      have hc : cF = c := by simpa [dt_nth_cons] using hnth
      subst c
      simp only [__smtx_datatype_bounded, native_and,
        Bool.and_eq_true] at hBnd
      exact hBnd.2.1
  | SmtDatatype.sum cF (SmtDatatype.sum c2 d2), Nat.succ k, c, hnth, hBnd => by
      have hnth' : dt_nth_cons (SmtDatatype.sum c2 d2) k = some c := by
        simpa [dt_nth_cons] using hnth
      simp only [__smtx_datatype_bounded, native_and,
        Bool.and_eq_true] at hBnd
      exact bounded_datatype_cons (SmtDatatype.sum c2 d2) k c hnth' hBnd.2.2

private theorem step_partial_sound (u : native_Bool) (dd : SmtDatatypeDecl)
    (hUniq : dd_unique dd) :
    ∀ (ddS B : SmtDatatypeDecl),
      SuffixOf ddS dd ->
      (∀ t : native_String, __smtx_dd_has_dt t B = true ->
        __smtx_datatype_bounded u (__smtx_dd_lookup t dd) B = true) ->
      ∀ t : native_String,
        __smtx_dd_has_dt t (__smtx_datatype_decl_bounded_step u ddS B) = true ->
          __smtx_datatype_bounded u (__smtx_dd_lookup t dd)
            (__smtx_datatype_decl_bounded_step u ddS B) = true
  | SmtDatatypeDecl.nil, B, _hSuf, hInv, t, hMem => by
      simp only [__smtx_datatype_decl_bounded_step] at hMem ⊢
      exact hInv t hMem
  | SmtDatatypeDecl.cons sF dF rest, B, hSuf, hInv, t, hMem => by
      simp only [__smtx_datatype_decl_bounded_step] at hMem ⊢
      by_cases hCond :
          (native_and (native_not (__smtx_dd_has_dt sF B))
            (__smtx_datatype_bounded u dF B)) = true
      · rw [native_ite, if_pos hCond] at hMem ⊢
        refine step_partial_sound u dd hUniq rest
          (SmtDatatypeDecl.cons sF dF B) (suffixOf_cons_inner hSuf) ?_ t hMem
        intro t' hMem'
        have hSub : SubDD B (SmtDatatypeDecl.cons sF dF B) :=
          subdd_cons sF dF B
        by_cases hts : native_streq t' sF = true
        · have hEq : t' = sF := by simpa [native_streq] using hts
          subst t'
          have hLk : __smtx_dd_lookup sF dd = dF :=
            suffix_head_lookup hSuf hUniq
          rw [hLk]
          simp only [native_and, Bool.and_eq_true] at hCond
          exact datatype_bounded_mono u hSub dF hCond.2
        · have hMem'' : __smtx_dd_has_dt t' B = true := by
            simpa [__smtx_dd_has_dt, native_or, hts] using hMem'
          exact datatype_bounded_mono u hSub _ (hInv t' hMem'')
      · rw [native_ite, if_neg hCond] at hMem ⊢
        exact step_partial_sound u dd hUniq rest B
          (suffixOf_cons_inner hSuf) hInv t hMem

private theorem decl_bounded_sound_aux (u : native_Bool) (dd : SmtDatatypeDecl)
    (hUniq : dd_unique dd) :
    ∀ (ddC B : SmtDatatypeDecl),
      (∀ t : native_String, __smtx_dd_has_dt t B = true ->
        __smtx_datatype_bounded u (__smtx_dd_lookup t dd) B = true) ->
      ∀ t : native_String,
        __smtx_dd_has_dt t (__smtx_datatype_decl_bounded u ddC dd B) = true ->
          __smtx_datatype_bounded u (__smtx_dd_lookup t dd)
            (__smtx_datatype_decl_bounded u ddC dd B) = true
  | SmtDatatypeDecl.nil, B, hInv, t, hMem => by
      simp only [__smtx_datatype_decl_bounded] at hMem ⊢
      exact hInv t hMem
  | SmtDatatypeDecl.cons sC dC ddC, B, hInv, t, hMem => by
      simp only [__smtx_datatype_decl_bounded] at hMem ⊢
      exact decl_bounded_sound_aux u dd hUniq ddC
        (__smtx_datatype_decl_bounded_step u dd B)
        (step_partial_sound u dd hUniq dd B (SuffixOf.refl dd) hInv) t hMem

/-- Everything in the fixpoint has a bounded body at the fixpoint. -/
private theorem bounded_fix_sound (u : native_Bool) (dd : SmtDatatypeDecl)
    (hUniq : dd_unique dd) (t : native_String)
    (hMem :
      __smtx_dd_has_dt t
        (__smtx_datatype_decl_bounded u dd dd SmtDatatypeDecl.nil) = true) :
    __smtx_datatype_bounded u (__smtx_dd_lookup t dd)
      (__smtx_datatype_decl_bounded u dd dd SmtDatatypeDecl.nil) = true := by
  refine decl_bounded_sound_aux u dd hUniq dd SmtDatatypeDecl.nil ?_ t hMem
  intro t' hMem'
  simp [__smtx_dd_has_dt] at hMem'

/--
Generic payload induction along the boundedness fixpoint: a property `P`
holds of every member of the fixpoint provided it can be established for an
entry whenever the entry's body is bounded at an accumulator all of whose
members already satisfy `P`.  This packages the addition-order induction:
at the moment an entry is added, its (bounded) fields refer only to
already-added members.
-/
theorem step_payload (u : native_Bool) (dd : SmtDatatypeDecl)
    (hUniq : dd_unique dd)
    (P : native_String -> Prop)
    (hStep : ∀ t : native_String,
      __smtx_dd_has_dt t dd = true ->
      ∀ B0 : SmtDatatypeDecl,
        __smtx_datatype_bounded u (__smtx_dd_lookup t dd) B0 = true ->
        (∀ r : native_String, __smtx_dd_has_dt r B0 = true -> P r) ->
        P t) :
    ∀ (ddS B : SmtDatatypeDecl),
      SuffixOf ddS dd ->
      (∀ t : native_String, __smtx_dd_has_dt t B = true -> P t) ->
      ∀ t : native_String,
        __smtx_dd_has_dt t (__smtx_datatype_decl_bounded_step u ddS B) = true ->
          P t
  | SmtDatatypeDecl.nil, B, _hSuf, hInv, t, hMem => by
      simp only [__smtx_datatype_decl_bounded_step] at hMem
      exact hInv t hMem
  | SmtDatatypeDecl.cons sF dF rest, B, hSuf, hInv, t, hMem => by
      simp only [__smtx_datatype_decl_bounded_step] at hMem
      by_cases hCond :
          (native_and (native_not (__smtx_dd_has_dt sF B))
            (__smtx_datatype_bounded u dF B)) = true
      · rw [native_ite, if_pos hCond] at hMem
        refine step_payload u dd hUniq P hStep rest
          (SmtDatatypeDecl.cons sF dF B) (suffixOf_cons_inner hSuf) ?_ t hMem
        intro t' hMem'
        by_cases hts : native_streq t' sF = true
        · have hEq : t' = sF := by simpa [native_streq] using hts
          subst t'
          have hLk : __smtx_dd_lookup sF dd = dF :=
            suffix_head_lookup hSuf hUniq
          have hMemDD : __smtx_dd_has_dt sF dd = true :=
            suffixOf_has_dt hSuf
              (by simp [__smtx_dd_has_dt, native_or, native_streq])
          simp only [native_and, Bool.and_eq_true] at hCond
          exact hStep sF hMemDD B (by rw [hLk]; exact hCond.2) hInv
        · have hMem'' : __smtx_dd_has_dt t' B = true := by
            simpa [__smtx_dd_has_dt, native_or, hts] using hMem'
          exact hInv t' hMem''
      · rw [native_ite, if_neg hCond] at hMem
        exact step_payload u dd hUniq P hStep rest B
          (suffixOf_cons_inner hSuf) hInv t hMem

private theorem decl_bounded_payload_aux (u : native_Bool) (dd : SmtDatatypeDecl)
    (hUniq : dd_unique dd)
    (P : native_String -> Prop)
    (hStep : ∀ t : native_String,
      __smtx_dd_has_dt t dd = true ->
      ∀ B0 : SmtDatatypeDecl,
        __smtx_datatype_bounded u (__smtx_dd_lookup t dd) B0 = true ->
        (∀ r : native_String, __smtx_dd_has_dt r B0 = true -> P r) ->
        P t) :
    ∀ (ddC B : SmtDatatypeDecl),
      (∀ t : native_String, __smtx_dd_has_dt t B = true -> P t) ->
      ∀ t : native_String,
        __smtx_dd_has_dt t (__smtx_datatype_decl_bounded u ddC dd B) = true ->
          P t
  | SmtDatatypeDecl.nil, B, hInv, t, hMem => by
      simp only [__smtx_datatype_decl_bounded] at hMem
      exact hInv t hMem
  | SmtDatatypeDecl.cons sC dC ddC, B, hInv, t, hMem => by
      simp only [__smtx_datatype_decl_bounded] at hMem
      exact decl_bounded_payload_aux u dd hUniq P hStep ddC
        (__smtx_datatype_decl_bounded_step u dd B)
        (step_payload u dd hUniq P hStep dd B (SuffixOf.refl dd) hInv) t hMem

/-- Payload induction over the full fixpoint. -/
theorem decl_bounded_payload (u : native_Bool) (dd : SmtDatatypeDecl)
    (hUniq : dd_unique dd)
    (P : native_String -> Prop)
    (hStep : ∀ t : native_String,
      __smtx_dd_has_dt t dd = true ->
      ∀ B0 : SmtDatatypeDecl,
        __smtx_datatype_bounded u (__smtx_dd_lookup t dd) B0 = true ->
        (∀ r : native_String, __smtx_dd_has_dt r B0 = true -> P r) ->
        P t) :
    ∀ t : native_String,
      __smtx_dd_has_dt t
        (__smtx_datatype_decl_bounded u dd dd SmtDatatypeDecl.nil) = true ->
        P t := by
  intro t hMem
  refine decl_bounded_payload_aux u dd hUniq P hStep dd
    SmtDatatypeDecl.nil ?_ t hMem
  intro t' hMem'
  simp [__smtx_dd_has_dt] at hMem'

theorem bounded_field_finite
    (dd : SmtDatatypeDecl) (F : SmtType)
    (hBnd : __smtx_field_type_bounded false F (bounded_fix dd) = true) :
    __smtx_is_finite_type (resolve_ty dd F) = true := by
  cases F <;>
    simp [__smtx_field_type_bounded, resolve_ty, __smtx_is_finite_type,
      __smtx_type_bounded, bounded_fix] at hBnd ⊢ <;>
    exact hBnd

/-- The unit fixpoint of a declaration. -/
def unit_fix (dd : SmtDatatypeDecl) : SmtDatatypeDecl :=
  __smtx_datatype_decl_bounded true dd dd SmtDatatypeDecl.nil

theorem is_unit_datatype_eq (s : native_String) (dd : SmtDatatypeDecl) :
    __smtx_is_unit_type (SmtType.Datatype s dd) =
      __smtx_dd_has_dt s (unit_fix dd) := by
  simp [__smtx_is_unit_type, __smtx_type_bounded, unit_fix]

theorem nonunit_field_nonunit
    (dd : SmtDatatypeDecl) (F : SmtType)
    (hUnb : __smtx_field_type_bounded true F (unit_fix dd) = false) :
    __smtx_is_unit_type (resolve_ty dd F) = false := by
  cases F <;>
    simp [__smtx_field_type_bounded, resolve_ty, __smtx_is_unit_type,
      __smtx_type_bounded, unit_fix] at hUnb ⊢ <;>
    exact hUnb

-- === spine head and injectivity ===

theorem vsm_apply_head_build_spine :
    ∀ (vs : List SmtValue) (f : SmtValue),
      __smtx_apply_head_value (build_spine f vs) = __smtx_apply_head_value f
  | [], f => by
      simp [build_spine]
  | v :: vs, f => by
      have := vsm_apply_head_build_spine vs (SmtValue.Apply f v)
      simpa [build_spine, __smtx_apply_head_value] using this

theorem build_spine_inj :
    ∀ (vs ws : List SmtValue) (f g : SmtValue),
      vs.length = ws.length ->
      build_spine f vs = build_spine g ws ->
      f = g ∧ vs = ws
  | [], [], f, g, _, hEq => ⟨by simpa [build_spine] using hEq, rfl⟩
  | [], w :: ws, f, g, hLen, _ => by
      simp at hLen
  | v :: vs, [], f, g, hLen, _ => by
      simp at hLen
  | v :: vs, w :: ws, f, g, hLen, hEq => by
      have hLen' : vs.length = ws.length := by simpa using hLen
      have hEq' :
          build_spine (SmtValue.Apply f v) vs =
            build_spine (SmtValue.Apply g w) ws := by
        simpa [build_spine] using hEq
      rcases build_spine_inj vs ws _ _ hLen' hEq' with ⟨hApply, hTail⟩
      injection hApply with hf hv
      exact ⟨hf, by rw [hv, hTail]⟩

-- === the spine form of generated constructor defaults ===

def restricted_slots (dd : SmtDatatypeDecl) (ddF : SmtDatatypeDecl) :
    List SmtType -> List SmtValue
  | [] => []
  | T :: Ts => __smtx_field_type_default dd T ddF :: restricted_slots dd ddF Ts

theorem restricted_slots_length (dd ddF : SmtDatatypeDecl) :
    ∀ Ts : List SmtType, (restricted_slots dd ddF Ts).length = Ts.length
  | [] => rfl
  | T :: Ts => by
      simp [restricted_slots, restricted_slots_length dd ddF Ts]

theorem cons_default_spine (dd ddF : SmtDatatypeDecl) :
    ∀ (c : SmtDatatypeCons) (v : SmtValue),
      __smtx_datatype_cons_default v dd c ddF ≠ SmtValue.NotValue ->
        __smtx_datatype_cons_default v dd c ddF =
          build_spine v (restricted_slots dd ddF (dtc_fields c)) ∧
        ∀ w ∈ restricted_slots dd ddF (dtc_fields c), w ≠ SmtValue.NotValue
  | SmtDatatypeCons.unit, v, _ => by
      constructor
      · simp [__smtx_datatype_cons_default, dtc_fields, restricted_slots,
          build_spine]
      · intro w hw
        simp [dtc_fields, restricted_slots] at hw
  | SmtDatatypeCons.cons T c, v, hNe => by
      rw [__smtx_datatype_cons_default] at hNe ⊢
      by_cases hv :
          native_veq (__smtx_field_type_default dd T ddF)
            SmtValue.NotValue = true
      · rw [native_ite, if_pos hv] at hNe
        exact absurd rfl hNe
      · rw [native_ite, if_neg hv] at hNe ⊢
        have hSlotNe : __smtx_field_type_default dd T ddF ≠ SmtValue.NotValue := by
          intro hEq
          rw [hEq, veq_refl_true] at hv
          exact hv rfl
        rcases cons_default_spine dd ddF c
            (SmtValue.Apply v (__smtx_field_type_default dd T ddF)) hNe with
          ⟨hSpine, hSlots⟩
        constructor
        · rw [hSpine]
          simp [dtc_fields, restricted_slots, build_spine]
        · intro w hw
          have hw' :
              w = __smtx_field_type_default dd T ddF ∨
                w ∈ restricted_slots dd ddF (dtc_fields c) := by
            simpa [dtc_fields, restricted_slots] using hw
          rcases hw' with hwT | hwc
          · subst w
            exact hSlotNe
          · exact hSlots w hwc

-- === size chains and slot helpers ===

private theorem defaults_of_length :
    ∀ Us : List SmtType, (defaults_of Us).length = Us.length
  | [] => rfl
  | U :: Us => by
      simp [defaults_of, defaults_of_length Us]

theorem restricted_slots_append (dd ddF : SmtDatatypeDecl) :
    ∀ (pre : List SmtType) (F : SmtType) (post : List SmtType),
      restricted_slots dd ddF (pre ++ F :: post) =
        restricted_slots dd ddF pre ++
          __smtx_field_type_default dd F ddF :: restricted_slots dd ddF post
  | [], F, post => by
      simp [restricted_slots]
  | T :: pre, F, post => by
      simp [restricted_slots, restricted_slots_append dd ddF pre F post]

private theorem sizeOf_lookup_lt (s : native_String) :
    ∀ dd2 : SmtDatatypeDecl,
      __smtx_dd_has_dt s dd2 = true ->
        sizeOf (__smtx_dd_lookup s dd2) < sizeOf dd2
  | SmtDatatypeDecl.nil, hMem => by
      simp [__smtx_dd_has_dt] at hMem
  | SmtDatatypeDecl.cons s2 d2 dd2, hMem => by
      by_cases hs : native_streq s s2 = true
      · have hLk : __smtx_dd_lookup s (SmtDatatypeDecl.cons s2 d2 dd2) = d2 := by
          simp [__smtx_dd_lookup, native_ite, hs]
        rw [hLk]
        rw [show sizeOf (SmtDatatypeDecl.cons s2 d2 dd2) =
          1 + sizeOf s2 + sizeOf d2 + sizeOf dd2 by rfl]
        omega
      · have hMem' : __smtx_dd_has_dt s dd2 = true := by
          simpa [__smtx_dd_has_dt, native_or, hs] using hMem
        have hLk :
            __smtx_dd_lookup s (SmtDatatypeDecl.cons s2 d2 dd2) =
              __smtx_dd_lookup s dd2 := by
          simp [__smtx_dd_lookup, native_ite, hs]
        rw [hLk]
        have := sizeOf_lookup_lt s dd2 hMem'
        rw [show sizeOf (SmtDatatypeDecl.cons s2 d2 dd2) =
          1 + sizeOf s2 + sizeOf d2 + sizeOf dd2 by rfl]
        omega

private theorem sizeOf_nth_cons_lt :
    ∀ (d : SmtDatatype) (k : Nat) (c : SmtDatatypeCons),
      dt_nth_cons d k = some c -> sizeOf c < sizeOf d
  | SmtDatatype.null, k, c, hnth => by
      simp [dt_nth_cons] at hnth
  | SmtDatatype.sum cF dF, 0, c, hnth => by
      have hc : cF = c := by simpa [dt_nth_cons] using hnth
      subst c
      rw [show sizeOf (SmtDatatype.sum cF dF) = 1 + sizeOf cF + sizeOf dF by rfl]
      omega
  | SmtDatatype.sum cF dF, Nat.succ k, c, hnth => by
      have hnth' : dt_nth_cons dF k = some c := by
        simpa [dt_nth_cons] using hnth
      have := sizeOf_nth_cons_lt dF k c hnth'
      rw [show sizeOf (SmtDatatype.sum cF dF) = 1 + sizeOf cF + sizeOf dF by rfl]
      omega

private theorem sizeOf_field_lt :
    ∀ (c : SmtDatatypeCons) (F : SmtType),
      F ∈ dtc_fields c -> sizeOf F < sizeOf c
  | SmtDatatypeCons.unit, F, hF => by
      simp [dtc_fields] at hF
  | SmtDatatypeCons.cons T c, F, hF => by
      have hF' : F = T ∨ F ∈ dtc_fields c := by
        simpa [dtc_fields] using hF
      rw [show sizeOf (SmtDatatypeCons.cons T c) = 1 + sizeOf T + sizeOf c by rfl]
      rcases hF' with hFT | hFc
      · subst F
        omega
      · have := sizeOf_field_lt c F hFc
        omega

theorem field_type_default_ref (dd ddF : SmtDatatypeDecl)
    (t : native_String) :
    __smtx_field_type_default dd (SmtType.TypeRef t) ddF =
      __smtx_datatype_decl_default t dd ddF := by
  simp [__smtx_field_type_default]

theorem field_type_default_ground (dd ddF : SmtDatatypeDecl)
    (F : SmtType) (hRef : ∀ t : native_String, F ≠ SmtType.TypeRef t) :
    __smtx_field_type_default dd F ddF = __smtx_type_default F := by
  cases F <;> first
    | exact absurd rfl (hRef _)
    | simp [__smtx_field_type_default]

theorem resolve_ty_ground (dd : SmtDatatypeDecl)
    (F : SmtType) (hRef : ∀ t : native_String, F ≠ SmtType.TypeRef t) :
    resolve_ty dd F = F := by
  cases F <;> first
    | exact absurd rfl (hRef _)
    | simp [resolve_ty]

theorem apply_head_dt_cons (s : native_String)
    (dd : SmtDatatypeDecl) (k : Nat) :
    __smtx_apply_head_value (SmtValue.DtCons s dd k) = SmtValue.DtCons s dd k := by
  simp [__smtx_apply_head_value]

/-- Typed canonical constructor spine over given field values. -/
theorem constructor_spine_typed
    (s : native_String) (dd : SmtDatatypeDecl) (k : Nat) (c : SmtDatatypeCons)
    (hnth : dt_nth_cons (__smtx_dd_lookup s dd) k = some c)
    (vs : List SmtValue)
    (hTyped : list_typed_canonical vs ((dtc_fields c).map (resolve_ty dd))) :
    __smtx_typeof_value (build_spine (SmtValue.DtCons s dd k) vs) =
        SmtType.Datatype s dd ∧
      __smtx_value_canonical (build_spine (SmtValue.DtCons s dd k) vs) =
        true ∧
      __smtx_apply_head_value (build_spine (SmtValue.DtCons s dd k) vs) =
        SmtValue.DtCons s dd k := by
  have hHeadTy :
      __smtx_typeof_value (SmtValue.DtCons s dd k) =
        dtc_chain_type (SmtType.Datatype s dd)
          ((dtc_fields c).map (resolve_ty dd)) := by
    have hTy :
        __smtx_typeof_value (SmtValue.DtCons s dd k) =
          __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s dd)
            (__smtx_dt_resolve (__smtx_dd_lookup s dd) dd) k := by
      simp [__smtx_typeof_value]
    rw [hTy,
      typeof_dt_cons_value_rec_nth (SmtType.Datatype s dd)
        (__smtx_dt_resolve (__smtx_dd_lookup s dd) dd) k
        (__smtx_dtc_resolve c dd)
        (dt_resolve_nth dd (__smtx_dd_lookup s dd) k c hnth),
      dtc_resolve_fields dd c]
  have hHeadCan :
      __smtx_value_canonical (SmtValue.DtCons s dd k) = true := by
    simp [__smtx_value_canonical]
  refine
    ⟨build_spine_typeof (SmtType.Datatype s dd) _ vs _ hHeadTy hTyped,
      build_spine_canonical _ vs _ hHeadCan hTyped,
      ?_⟩
  rw [vsm_apply_head_build_spine vs (SmtValue.DtCons s dd k)]
  exact apply_head_dt_cons s dd k

/-- All-default typed canonical constructor spine. -/
theorem constructor_default_spine
    (s : native_String) (dd : SmtDatatypeDecl) (k : Nat) (c : SmtDatatypeCons)
    (hDecl : __smtx_decl_wf_rec dd dd = true)
    (hnth : dt_nth_cons (__smtx_dd_lookup s dd) k = some c)
    (hConsWf : __smtx_dt_cons_wf_rec dd c = true) :
    ∃ v : SmtValue,
      __smtx_typeof_value v = SmtType.Datatype s dd ∧
        __smtx_value_canonical v = true ∧
        __smtx_apply_head_value v = SmtValue.DtCons s dd k := by
  have hWfAll :
      ∀ U ∈ (dtc_fields c).map (resolve_ty dd),
        native_inhabited_type U = true ∧ __smtx_type_wf_rec U = true := by
    intro U hU
    rcases List.mem_map.mp hU with ⟨F', hF'mem, hF'eq⟩
    rw [← hF'eq]
    exact resolved_field_inh_wf dd hDecl c hConsWf F' hF'mem
  have hTyped :=
    list_typed_canonical_defaults ((dtc_fields c).map (resolve_ty dd)) hWfAll
  rcases constructor_spine_typed s dd k c hnth
      (defaults_of ((dtc_fields c).map (resolve_ty dd))) hTyped with
    ⟨hTy, hCan, hHead⟩
  exact ⟨_, hTy, hCan, hHead⟩

-- === the finite non-unit witness ===

mutual

/-- Non-default typed canonical value of a finite non-unit datatype. -/
private theorem dt_nondefault
    (s : native_String) (dd : SmtDatatypeDecl)
    (hInh : native_inhabited_type (SmtType.Datatype s dd) = true)
    (hRec : __smtx_type_wf_rec (SmtType.Datatype s dd) = true)
    (hFinite : __smtx_is_finite_type (SmtType.Datatype s dd) = true)
    (hNonUnit : __smtx_is_unit_type (SmtType.Datatype s dd) = false) :
    ∃ e : SmtValue,
      __smtx_typeof_value e = SmtType.Datatype s dd ∧
        __smtx_value_canonical e = true ∧
          native_veq e (__smtx_type_default (SmtType.Datatype s dd)) = false := by
  have hRecParts :
      __smtx_dd_has_dt s dd = true ∧ __smtx_decl_wf_rec dd dd = true := by
    simpa [__smtx_type_wf_rec, native_and] using hRec
  have hUniq : dd_unique dd := dd_unique_of_decl_wf dd dd hRecParts.2
  have hDtWf : __smtx_dt_wf_rec dd (__smtx_dd_lookup s dd) = true :=
    decl_wf_rec_lookup_local s dd dd hRecParts.1 hRecParts.2
  have hNotUnitFix : __smtx_dd_has_dt s (unit_fix dd) = false := by
    rw [is_unit_datatype_eq] at hNonUnit
    exact hNonUnit
  have hUnbLookup :
      __smtx_datatype_bounded true (__smtx_dd_lookup s dd)
        (unit_fix dd) = false :=
    unbounded_lookup_of_not_fix true dd s hRecParts.1 hNotUnitFix
  have hFixMem : __smtx_dd_has_dt s (bounded_fix dd) = true := by
    rw [is_finite_datatype_eq] at hFinite
    exact hFinite
  have hFixBnd :
      __smtx_datatype_bounded false (__smtx_dd_lookup s dd)
        (bounded_fix dd) = true :=
    bounded_fix_sound false dd hUniq s hFixMem
  cases hd : __smtx_dd_lookup s dd with
  | null =>
      exfalso
      have hDef :
          __smtx_type_default (SmtType.Datatype s dd) = SmtValue.NotValue := by
        have := decl_default_of_lookup_null s dd dd hd
        simpa [__smtx_type_default] using this
      have hTy := type_default_typed_of_inhabited _ hInh
      rw [hDef] at hTy
      simp [__smtx_typeof_value] at hTy
  | sum c dRest =>
      cases dRest with
      | sum c2 d2 =>
          -- at least two constructors: two spines with distinct heads
          have hnth0 :
              dt_nth_cons (__smtx_dd_lookup s dd) 0 = some c := by
            rw [hd]
            rfl
          have hnth1 :
              dt_nth_cons (__smtx_dd_lookup s dd) 1 = some c2 := by
            rw [hd]
            rfl
          have hConsWf0 :=
            dt_wf_nth_cons dd (__smtx_dd_lookup s dd) 0 c hnth0 hDtWf
          have hConsWf1 :=
            dt_wf_nth_cons dd (__smtx_dd_lookup s dd) 1 c2 hnth1 hDtWf
          rcases constructor_default_spine s dd 0 c hRecParts.2 hnth0 hConsWf0
            with ⟨v0, hv0Ty, hv0Can, hv0Head⟩
          rcases constructor_default_spine s dd 1 c2 hRecParts.2 hnth1 hConsWf1
            with ⟨v1, hv1Ty, hv1Can, hv1Head⟩
          have hNe01 : v0 ≠ v1 := by
            intro hEq
            rw [hEq, hv1Head] at hv0Head
            injection hv0Head with _ _ h01
            cases h01
          cases h0 :
              native_veq v0 (__smtx_type_default (SmtType.Datatype s dd)) with
          | false =>
              exact ⟨v0, hv0Ty, hv0Can, h0⟩
          | true =>
              have hv0Def := veq_eq_of_true h0
              refine ⟨v1, hv1Ty, hv1Can, ?_⟩
              cases h1 :
                  native_veq v1 (__smtx_type_default (SmtType.Datatype s dd)) with
              | false => rfl
              | true =>
                  have hv1Def := veq_eq_of_true h1
                  exact absurd (hv0Def.trans hv1Def.symm) hNe01
      | null =>
          -- single constructor: replace the designated non-unit field
          have hConsUnb :
              __smtx_datatype_cons_bounded true c (unit_fix dd) = false := by
            simpa [__smtx_datatype_bounded, hd] using hUnbLookup
          have hConsBnd :
              __smtx_datatype_cons_bounded false c (bounded_fix dd) = true := by
            simpa [__smtx_datatype_bounded, hd] using hFixBnd
          have hnth0 :
              dt_nth_cons (__smtx_dd_lookup s dd) 0 = some c := by
            rw [hd]
            rfl
          have hConsWf :=
            dt_wf_nth_cons dd (__smtx_dd_lookup s dd) 0 c hnth0 hDtWf
          rcases unbounded_cons_has_unbounded_field c hConsUnb with
            ⟨pre, F, post, hFields, hFieldUnb⟩
          have hFmem : F ∈ dtc_fields c := by
            rw [hFields]
            simp
          have hFieldBnd :
              __smtx_field_type_bounded false F (bounded_fix dd) = true :=
            bounded_cons_field c hConsBnd F hFmem
          have hXWf := resolved_field_inh_wf dd hRecParts.2 c hConsWf F hFmem
          have hXNonUnit := nonunit_field_nonunit dd F hFieldUnb
          have hXFinite := bounded_field_finite dd F hFieldBnd
          -- the scan structure of the default
          rcases decl_default_find s dd dd hRecParts.1 with
            ⟨ddTail, hSuf, hDefEq⟩
          have hDefaultRaw :
              __smtx_type_default (SmtType.Datatype s dd) =
                __smtx_datatype_decl_default s dd dd := by
            simp [__smtx_type_default]
          have hDefNe :
              __smtx_type_default (SmtType.Datatype s dd) ≠
                SmtValue.NotValue :=
            default_ne_notValue_of_inh hInh
          have hSufTail : SuffixOf ddTail dd := by
            rw [hd] at hSuf
            exact suffixOf_cons_inner hSuf
          -- the default is the constructor-zero restricted spine
          have hDefaultR :
              __smtx_type_default (SmtType.Datatype s dd) =
                __smtx_datatype_cons_default (SmtValue.DtCons s dd 0) dd c
                  ddTail := by
            rw [hDefaultRaw, hDefEq, hd]
            cases hr :
                native_veq
                  (__smtx_datatype_cons_default (SmtValue.DtCons s dd 0) dd c
                    ddTail)
                  SmtValue.NotValue with
            | false =>
                simp [__smtx_datatype_default, native_ite, native_not, hr]
            | true =>
                exfalso
                apply hDefNe
                rw [hDefaultRaw, hDefEq, hd]
                have hrEq := veq_eq_of_true hr
                simp [__smtx_datatype_default, native_ite, native_not, hr,
                  hrEq]
          have hRNe :
              __smtx_datatype_cons_default (SmtValue.DtCons s dd 0) dd c
                  ddTail ≠ SmtValue.NotValue := by
            rw [← hDefaultR]
            exact hDefNe
          rcases cons_default_spine dd ddTail c (SmtValue.DtCons s dd 0) hRNe
            with ⟨hSpineEq, hSlotsNe⟩
          -- identify the designated slot with the resolved field default
          have hSlotMem :
              __smtx_field_type_default dd F ddTail ∈
                restricted_slots dd ddTail (dtc_fields c) := by
            rw [hFields, restricted_slots_append]
            simp
          have hSlotEq :
              __smtx_field_type_default dd F ddTail =
                __smtx_type_default (resolve_ty dd F) := by
            by_cases hRef : ∃ t : native_String, F = SmtType.TypeRef t
            · rcases hRef with ⟨t, hFt⟩
              subst F
              have hSlotNe :
                  __smtx_datatype_decl_default t dd ddTail ≠
                    SmtValue.NotValue := by
                have := hSlotsNe _ hSlotMem
                rw [field_type_default_ref] at this
                exact this
              have hMemTail :
                  __smtx_dd_has_dt t ddTail = true :=
                decl_default_has_dt_of_ne_notValue t dd ddTail hSlotNe
              rw [field_type_default_ref,
                suffix_decl_default_eq t dd hSufTail hUniq hMemTail]
              simp [resolve_ty, __smtx_type_default]
            · have hRef' : ∀ t : native_String, F ≠ SmtType.TypeRef t := by
                intro t hFt
                exact hRef ⟨t, hFt⟩
              rw [field_type_default_ground dd ddTail F hRef',
                resolve_ty_ground dd F hRef']
          -- non-default value of the designated field type
          have hEF :
              ∃ eF : SmtValue,
                __smtx_typeof_value eF = resolve_ty dd F ∧
                  __smtx_value_canonical eF = true ∧
                    native_veq eF
                      (__smtx_type_default (resolve_ty dd F)) = false := by
            by_cases hRef : ∃ t : native_String, F = SmtType.TypeRef t
            · rcases hRef with ⟨t, hFt⟩
              subst F
              -- sibling reference: recurse on the strictly smaller default
              have hMeasure :
                  sizeOf (__smtx_type_default (SmtType.Datatype t dd)) <
                    sizeOf (__smtx_type_default (SmtType.Datatype s dd)) := by
                have hSlotSize :=
                  build_spine_size_ge_mem
                    (restricted_slots dd ddTail (dtc_fields c))
                    (SmtValue.DtCons s dd 0) _ hSlotMem
                rw [← hSpineEq, ← hDefaultR] at hSlotSize
                have hSlotIsDefault :
                    __smtx_field_type_default dd (SmtType.TypeRef t) ddTail =
                      __smtx_type_default (SmtType.Datatype t dd) := by
                  rw [hSlotEq]
                  simp [resolve_ty]
                rw [hSlotIsDefault] at hSlotSize
                omega
              have hXWf' := hXWf
              have hXNonUnit' := hXNonUnit
              have hXFinite' := hXFinite
              simp only [resolve_ty] at hXWf' hXNonUnit' hXFinite' ⊢
              exact dt_nondefault t dd hXWf'.1 hXWf'.2 hXFinite' hXNonUnit'
            · have hRef' : ∀ t : native_String, F ≠ SmtType.TypeRef t := by
                intro t hFt
                exact hRef ⟨t, hFt⟩
              have hMeasure : sizeOf F < sizeOf dd := by
                have h1 := sizeOf_field_lt c F hFmem
                have h2 := sizeOf_nth_cons_lt (__smtx_dd_lookup s dd) 0 c hnth0
                have h3 := sizeOf_lookup_lt s dd hRecParts.1
                omega
              have hXWf' := hXWf
              have hXNonUnit' := hXNonUnit
              have hXFinite' := hXFinite
              rw [resolve_ty_ground dd F hRef'] at hXWf' hXNonUnit' hXFinite' ⊢
              exact ty_nondefault F hXWf'.1 hXWf'.2 hXFinite' hXNonUnit'
          rcases hEF with ⟨eF, heTy, heCan, heNe⟩
          -- assemble the witness spine
          have hMapFields :
              (dtc_fields c).map (resolve_ty dd) =
                pre.map (resolve_ty dd) ++
                  resolve_ty dd F :: post.map (resolve_ty dd) := by
            rw [hFields]
            simp
          have hPreWf :
              ∀ U ∈ pre.map (resolve_ty dd),
                native_inhabited_type U = true ∧
                  __smtx_type_wf_rec U = true := by
            intro U hU
            rcases List.mem_map.mp hU with ⟨F', hF'mem, hF'eq⟩
            rw [← hF'eq]
            exact resolved_field_inh_wf dd hRecParts.2 c hConsWf F'
              (by rw [hFields]; simp [hF'mem])
          have hPostWf :
              ∀ U ∈ post.map (resolve_ty dd),
                native_inhabited_type U = true ∧
                  __smtx_type_wf_rec U = true := by
            intro U hU
            rcases List.mem_map.mp hU with ⟨F', hF'mem, hF'eq⟩
            rw [← hF'eq]
            exact resolved_field_inh_wf dd hRecParts.2 c hConsWf F'
              (by rw [hFields]; simp [hF'mem])
          have hXNone : resolve_ty dd F ≠ SmtType.None :=
            ne_none_of_inh hXWf.1
          have hTyped :
              list_typed_canonical
                (defaults_of (pre.map (resolve_ty dd)) ++
                  eF :: defaults_of (post.map (resolve_ty dd)))
                ((dtc_fields c).map (resolve_ty dd)) := by
            rw [hMapFields]
            exact list_typed_canonical_append
              (list_typed_canonical_defaults _ hPreWf)
              ⟨⟨heTy, hXNone, heCan⟩,
                list_typed_canonical_defaults _ hPostWf⟩
          rcases constructor_spine_typed s dd 0 c hnth0 _ hTyped with
            ⟨hvTy, hvCan, _hvHead⟩
          refine ⟨_, hvTy, hvCan, ?_⟩
          -- the witness differs from the default at the designated slot
          cases hveq :
              native_veq
                (build_spine (SmtValue.DtCons s dd 0)
                  (defaults_of (pre.map (resolve_ty dd)) ++
                    eF :: defaults_of (post.map (resolve_ty dd))))
                (__smtx_type_default (SmtType.Datatype s dd)) with
          | false => rfl
          | true =>
              exfalso
              have hvEq := veq_eq_of_true hveq
              rw [hDefaultR, hSpineEq] at hvEq
              have hSlotsSplit :=
                restricted_slots_append dd ddTail pre F post
              have hLen :
                  (defaults_of (pre.map (resolve_ty dd)) ++
                    eF :: defaults_of (post.map (resolve_ty dd))).length =
                    (restricted_slots dd ddTail (dtc_fields c)).length := by
                rw [restricted_slots_length, hFields]
                simp [defaults_of_length]
              rcases build_spine_inj _ _ _ _ hLen hvEq with ⟨_, hLists⟩
              rw [hFields, hSlotsSplit] at hLists
              have hPreLen :
                  (defaults_of (pre.map (resolve_ty dd))).length =
                    (restricted_slots dd ddTail pre).length := by
                rw [restricted_slots_length, defaults_of_length]
                simp
              rcases List.append_inj hLists hPreLen with ⟨_, hMid⟩
              injection hMid with hHead _
              rw [hHead, hSlotEq, veq_refl_true] at heNe
              cases heNe
termination_by (sizeOf dd, sizeOf (__smtx_type_default (SmtType.Datatype s dd)))
decreasing_by
  · exact Prod.Lex.right (sizeOf dd) hMeasure
  · exact Prod.Lex.left _ _ hMeasure

/-- Non-default typed canonical value of a finite non-unit type. -/
private theorem ty_nondefault
    (A : SmtType)
    (_hInh : native_inhabited_type A = true)
    (_hRec : __smtx_type_wf_rec A = true)
    (_hFinite : __smtx_is_finite_type A = true)
    (_hNonUnit : __smtx_is_unit_type A = false) :
    ∃ e : SmtValue,
      __smtx_typeof_value e = A ∧
        __smtx_value_canonical e = true ∧
          native_veq e (__smtx_type_default A) = false := by
  cases A with
  | None =>
      simp [__smtx_type_wf_rec] at _hRec
  | Bool =>
      refine ⟨SmtValue.Boolean true, ?_, ?_, ?_⟩ <;>
        simp [__smtx_typeof_value, __smtx_value_canonical,
          __smtx_type_default, native_veq]
  | Int =>
      simp [__smtx_is_finite_type, __smtx_type_bounded] at _hFinite
  | Real =>
      simp [__smtx_is_finite_type, __smtx_type_bounded] at _hFinite
  | RegLan =>
      simp [__smtx_type_wf_rec] at _hRec
  | BitVec w =>
      cases w with
      | zero =>
          rw [is_unit_bitvec_eq_p] at _hNonUnit
          simp [native_nateq] at _hNonUnit
      | succ w =>
          exact
            ⟨SmtValue.Binary (native_nat_to_int (Nat.succ w)) 1,
              bitvec_succ_one_typeof_p w, bitvec_succ_one_canonical_p w,
              bitvec_succ_one_ne_default_p w⟩
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
        rw [is_unit_map_eq_p] at _hNonUnit
        exact _hNonUnit
      have hUFinite : __smtx_is_finite_type U = true := by
        rw [is_finite_map_eq_p] at _hFinite
        cases hU : __smtx_is_finite_type U
        · simp [native_or, native_and, hUNonUnit, hU] at _hFinite
        · rfl
      have hTDefault :=
        type_default_typed_canonical_p hRecParts.1 hRecParts.2.1
      have hUDefault :=
        type_default_typed_canonical_p hRecParts.2.2.1 hRecParts.2.2.2
      rcases ty_nondefault U hRecParts.2.2.1 hRecParts.2.2.2 hUFinite
          hUNonUnit with ⟨e, heTy, heCan, heNeDefault⟩
      have heNeDefaultProp : e ≠ __smtx_type_default U := by
        intro hEq
        subst e
        simp [native_veq] at heNeDefault
      have hUNV : __smtx_type_default U ≠ SmtValue.NotValue :=
        default_ne_notValue_of_inh hRecParts.2.2.1
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
        type_default_typed_canonical_p hRecParts.1 hRecParts.2
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
      simp [__smtx_is_finite_type, __smtx_type_bounded] at _hFinite
  | Char =>
      refine ⟨SmtValue.Char 1, ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value, native_char_valid, native_ite]
      · simp [__smtx_value_canonical, native_char_valid]
      · simp [__smtx_type_default, native_veq]
  | Datatype s2 dd2 =>
      exact dt_nondefault s2 dd2 _hInh _hRec _hFinite _hNonUnit
  | TypeRef s2 =>
      simp [__smtx_type_wf_rec] at _hRec
  | USort u =>
      simp [__smtx_is_finite_type, __smtx_type_bounded] at _hFinite
  | FunType T U =>
      simp [__smtx_type_wf_rec] at _hRec
  | DtcAppType T U =>
      simp [__smtx_type_wf_rec] at _hRec
termination_by (sizeOf A, 0)
decreasing_by
  · apply Prod.Lex.left
    subst A
    rw [show sizeOf (SmtType.Map T U) = 1 + sizeOf T + sizeOf U by rfl]
    omega
  · apply Prod.Lex.left
    subst A
    rw [show sizeOf (SmtType.Datatype s2 dd2) =
      1 + sizeOf s2 + sizeOf dd2 by rfl]
    omega

end

-- === the residual finite-datatype obligation, discharged ===

/--
A finite non-unit datatype has a typed canonical value different from its
default.
-/
theorem finite_nonunit_datatype_nondefault_value
    (s : native_String) (dd : SmtDatatypeDecl)
    (hInh : native_inhabited_type (SmtType.Datatype s dd) = true)
    (hRec : __smtx_type_wf_rec (SmtType.Datatype s dd) = true)
    (hFinite : __smtx_is_finite_type (SmtType.Datatype s dd) = true)
    (hNonUnit : __smtx_is_unit_type (SmtType.Datatype s dd) = false) :
    ∃ e : SmtValue,
      __smtx_typeof_value e = SmtType.Datatype s dd ∧
        __smtx_value_canonical e = true ∧
          native_veq e (__smtx_type_default (SmtType.Datatype s dd)) = false :=
  dt_nondefault s dd hInh hRec hFinite hNonUnit

/--
Every inhabited well-formed finite non-unit type has a typed canonical value
different from its default.
-/
private theorem finite_nonunit_nondefault
    (A : SmtType)
    (_hInh : native_inhabited_type A = true)
    (_hRec : __smtx_type_wf_rec A = true)
    (_hFinite : __smtx_is_finite_type A = true)
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
      simp [__smtx_is_finite_type, __smtx_type_bounded] at _hFinite
  | Real =>
      simp [__smtx_is_finite_type, __smtx_type_bounded] at _hFinite
  | RegLan =>
      simp [__smtx_type_wf_rec] at _hRec
  | BitVec w =>
      cases w with
      | zero =>
          rw [is_unit_bitvec_eq_p] at _hNonUnit
          simp [native_nateq] at _hNonUnit
      | succ w =>
          exact
            ⟨SmtValue.Binary (native_nat_to_int (Nat.succ w)) 1,
              bitvec_succ_one_typeof_p w, bitvec_succ_one_canonical_p w,
              bitvec_succ_one_ne_default_p w⟩
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
        rw [is_unit_map_eq_p] at _hNonUnit
        exact _hNonUnit
      have hUFinite : __smtx_is_finite_type U = true := by
        rw [is_finite_map_eq_p] at _hFinite
        cases hU : __smtx_is_finite_type U
        · simp [native_or, native_and, hUNonUnit, hU] at _hFinite
        · rfl
      have hTDefault :=
        type_default_typed_canonical_p hRecParts.1 hRecParts.2.1
      have hUDefault :=
        type_default_typed_canonical_p hRecParts.2.2.1 hRecParts.2.2.2
      rcases finite_nonunit_nondefault
          U hRecParts.2.2.1 hRecParts.2.2.2 hUFinite hUNonUnit with
        ⟨e, heTy, heCan, heNeDefault⟩
      have heNeDefaultProp : e ≠ __smtx_type_default U := by
        intro hEq
        subst e
        simp [native_veq] at heNeDefault
      have hUNV : __smtx_type_default U ≠ SmtValue.NotValue :=
        default_ne_notValue_of_inh hRecParts.2.2.1
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
        type_default_typed_canonical_p hRecParts.1 hRecParts.2
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
      simp [__smtx_is_finite_type, __smtx_type_bounded] at _hFinite
  | Char =>
      refine ⟨SmtValue.Char 1, ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value, native_char_valid, native_ite]
      · simp [__smtx_value_canonical, native_char_valid]
      · simp [__smtx_type_default, native_veq]
  | Datatype s dd =>
      exact finite_nonunit_datatype_nondefault_value
        s dd _hInh _hRec _hFinite _hNonUnit
  | TypeRef s =>
      simp [__smtx_type_wf_rec] at _hRec
  | USort u =>
      simp [__smtx_is_finite_type, __smtx_type_bounded] at _hFinite
  | FunType T U =>
      simp [__smtx_type_wf_rec] at _hRec
  | DtcAppType T U =>
      simp [__smtx_type_wf_rec] at _hRec
termination_by sizeOf A

-- === large values of arbitrary infinite types, given the oracle ===

private theorem type_large
    (n : Nat) (hO : LargeOracle n) (A : SmtType) :
    native_inhabited_type A = true →
    __smtx_type_wf_rec A = true →
    __smtx_is_finite_type A = false →
    ∃ v : SmtValue,
      __smtx_typeof_value v = A ∧
        __smtx_value_canonical v = true ∧ n ≤ sizeOf v := by
  cases A with
  | None =>
      intro _hInh hRec _hInf
      simp [__smtx_type_wf_rec] at hRec
  | Bool =>
      intro _hInh _hRec hInf
      simp [__smtx_is_finite_type, __smtx_type_bounded, native_not] at hInf
  | Int =>
      intro _ _ _
      exact int_large_witness_p n
  | Real =>
      intro _ _ _
      exact real_large_witness_p n
  | RegLan =>
      intro _hInh hRec _hInf
      simp [__smtx_type_wf_rec] at hRec
  | BitVec w =>
      intro _hInh _hRec hInf
      simp [__smtx_is_finite_type, __smtx_type_bounded, native_or,
        native_not] at hInf
  | Char =>
      intro _hInh _hRec hInf
      simp [__smtx_is_finite_type, __smtx_type_bounded, native_not] at hInf
  | Map T U =>
      intro hInh hRec hInf
      have hRecParts :
          native_inhabited_type T = true ∧
            __smtx_type_wf_rec T = true ∧
              native_inhabited_type U = true ∧
                __smtx_type_wf_rec U = true := by
        have h := hRec
        simp [__smtx_type_wf_rec, native_and] at h
        exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩
      have hTDefault :=
        type_default_typed_canonical_p hRecParts.1 hRecParts.2.1
      have hUDefault :=
        type_default_typed_canonical_p hRecParts.2.2.1 hRecParts.2.2.2
      have hUNonUnit : __smtx_is_unit_type U = false := by
        rw [is_finite_map_eq_p] at hInf
        cases hU : __smtx_is_unit_type U
        · rfl
        · simp [native_or, hU] at hInf
      by_cases hUInf : __smtx_is_finite_type U = false
      · -- large range value
        rcases type_large n hO U hRecParts.2.2.1 hRecParts.2.2.2 hUInf with
          ⟨e, heTy, heCan, heSize⟩
        cases hveq : native_veq e (__smtx_type_default U) with
        | false =>
            refine
              ⟨SmtValue.Map
                (SmtMap.cons (__smtx_type_default T) e
                  (SmtMap.default T (__smtx_type_default U))), ?_, ?_, ?_⟩
            · simp [__smtx_typeof_value, __smtx_typeof_map_value,
                hTDefault.1, heTy, hUDefault.1, native_ite, native_Teq]
            · have hNe : e ≠ __smtx_type_default U := by
                intro hEq
                subst e
                rw [veq_refl_true] at hveq
                cases hveq
              simp [__smtx_value_canonical, __smtx_map_canonical,
                __smtx_map_default_canonical, __smtx_map_entries_ordered_after,
                __smtx_map_get_default, hTDefault.2, heCan, hUDefault.1,
                hUDefault.2, hNe, native_and, native_ite, native_not,
                native_veq]
            · rw [show
                sizeOf
                    (SmtValue.Map
                      (SmtMap.cons (__smtx_type_default T) e
                        (SmtMap.default T (__smtx_type_default U)))) =
                  1 + (1 + sizeOf (__smtx_type_default T) + sizeOf e +
                    sizeOf (SmtMap.default T (__smtx_type_default U))) by rfl]
              omega
        | true =>
            -- the large value coincides with the default range value, so the
            -- default map itself is large
            have hEq : e = __smtx_type_default U := veq_eq_of_true hveq
            subst e
            refine
              ⟨SmtValue.Map (SmtMap.default T (__smtx_type_default U)),
                ?_, ?_, ?_⟩
            · simp [__smtx_typeof_value, __smtx_typeof_map_value, hUDefault.1]
            · simp [__smtx_value_canonical, __smtx_map_canonical,
                __smtx_map_default_canonical, hUDefault.1, hUDefault.2,
                native_and, native_ite, native_veq]
            · rw [show
                sizeOf
                    (SmtValue.Map (SmtMap.default T (__smtx_type_default U))) =
                  1 + (1 + sizeOf T + sizeOf (__smtx_type_default U)) by rfl]
              omega
      · -- finite range: the domain is infinite, use a large key
        have hUFin : __smtx_is_finite_type U = true := by
          cases hU : __smtx_is_finite_type U
          · exact absurd hU hUInf
          · rfl
        have hTInf : __smtx_is_finite_type T = false := by
          rw [is_finite_map_eq_p] at hInf
          cases hT : __smtx_is_finite_type T
          · rfl
          · simp [native_or, native_and, hT, hUFin, hUNonUnit] at hInf
        rcases type_large n hO T hRecParts.1 hRecParts.2.1 hTInf with
          ⟨k, hkTy, hkCan, hkSize⟩
        rcases finite_nonunit_nondefault
            U hRecParts.2.2.1 hRecParts.2.2.2 hUFin hUNonUnit with
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
        · rw [show
            sizeOf
                (SmtValue.Map
                  (SmtMap.cons k e
                    (SmtMap.default T (__smtx_type_default U)))) =
              1 + (1 + sizeOf k + sizeOf e +
                sizeOf (SmtMap.default T (__smtx_type_default U))) by rfl]
          omega
  | Set T =>
      intro hInh hRec hInf
      have hRecParts :
          native_inhabited_type T = true ∧
            __smtx_type_wf_rec T = true := by
        have h := hRec
        simp [__smtx_type_wf_rec, native_and] at h
        exact h
      have hTInf : __smtx_is_finite_type T = false := by
        rw [is_finite_set_eq_p] at hInf
        exact hInf
      rcases type_large n hO T hRecParts.1 hRecParts.2 hTInf with
        ⟨x, hxTy, hxCan, hxSize⟩
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
      · rw [show
          sizeOf
              (SmtValue.Set
                (SmtMap.cons x (SmtValue.Boolean true)
                  (SmtMap.default T (SmtValue.Boolean false)))) =
            1 + (1 + sizeOf x + sizeOf (SmtValue.Boolean true) +
              sizeOf (SmtMap.default T (SmtValue.Boolean false))) by rfl]
        omega
  | Seq T =>
      intro hInh hRec _hInf
      have hRecParts :
          native_inhabited_type T = true ∧
            __smtx_type_wf_rec T = true := by
        have h := hRec
        simp [__smtx_type_wf_rec, native_and] at h
        exact h
      exact seq_large_witness_p T hRecParts.1 hRecParts.2 n
  | Datatype s dd =>
      intro hInh hRec hInf
      exact hO s dd hInh hRec hInf
  | TypeRef s =>
      intro _hInh hRec _hInf
      simp [__smtx_type_wf_rec] at hRec
  | USort u =>
      intro _ _ _
      exact usort_large_witness_p u n
  | FunType T U =>
      intro _hInh hRec _hInf
      simp [__smtx_type_wf_rec] at hRec
  | DtcAppType T U =>
      intro _hInh hRec _hInf
      simp [__smtx_type_wf_rec] at hRec
termination_by sizeOf A

-- === the pump ===

private theorem oracle_zero : LargeOracle 0 := by
  intro s dd hInh hRec _hInf
  have hKernel := type_default_kernel (SmtType.Datatype s dd) hInh hRec
  exact ⟨__smtx_type_default (SmtType.Datatype s dd), hKernel.1, hKernel.2,
    Nat.zero_le _⟩

private theorem oracle_succ (n : Nat) (hO : LargeOracle n) :
    LargeOracle (Nat.succ n) := by
  intro s dd hInh hRec hInf
  rcases infinite_datatype_unbounded_constructor s dd hRec hInf with
    ⟨k, preU, postU, X, hChain, hAllWf, hXInf⟩
  have hXWf := hAllWf X (by simp)
  rcases type_large n hO X hXWf.1 hXWf.2 hXInf with ⟨w, hwTy, hwCan, hwSize⟩
  have hXNone : X ≠ SmtType.None := ne_none_of_inh hXWf.1
  have hPreWf :
      ∀ U ∈ preU, native_inhabited_type U = true ∧
        __smtx_type_wf_rec U = true := by
    intro U hU
    exact hAllWf U (by simp [hU])
  have hPostWf :
      ∀ U ∈ postU, native_inhabited_type U = true ∧
        __smtx_type_wf_rec U = true := by
    intro U hU
    exact hAllWf U (by simp [hU])
  have hTyped :
      list_typed_canonical
        (defaults_of preU ++ w :: defaults_of postU)
        (preU ++ X :: postU) :=
    list_typed_canonical_append
      (list_typed_canonical_defaults preU hPreWf)
      ⟨⟨hwTy, hXNone, hwCan⟩, list_typed_canonical_defaults postU hPostWf⟩
  have hHeadCan :
      __smtx_value_canonical (SmtValue.DtCons s dd k) = true := by
    simp [__smtx_value_canonical]
  refine
    ⟨build_spine (SmtValue.DtCons s dd k)
      (defaults_of preU ++ w :: defaults_of postU), ?_, ?_, ?_⟩
  · exact build_spine_typeof (SmtType.Datatype s dd)
      (preU ++ X :: postU) _ _ hChain hTyped
  · exact build_spine_canonical (preU ++ X :: postU) _ _ hHeadCan hTyped
  · have hMem : w ∈ defaults_of preU ++ w :: defaults_of postU := by
      simp
    have := build_spine_size_ge_mem
      (defaults_of preU ++ w :: defaults_of postU)
      (SmtValue.DtCons s dd k) w hMem
    omega

private theorem oracle_all : ∀ n : Nat, LargeOracle n
  | 0 => oracle_zero
  | Nat.succ n => oracle_succ n (oracle_all n)

/--
The infinite-datatype pump: an inhabited recursively well-formed datatype
outside the finiteness fixpoint has typed canonical values of arbitrarily
large size.
-/
theorem infinite_datatype_large_witness
    (minSize : Nat) (s : native_String) (dd : SmtDatatypeDecl)
    (hInh : native_inhabited_type (SmtType.Datatype s dd) = true)
    (hRec : __smtx_type_wf_rec (SmtType.Datatype s dd) = true)
    (hInfinite : __smtx_is_finite_type (SmtType.Datatype s dd) = false) :
    ∃ v : SmtValue,
      __smtx_typeof_value v = SmtType.Datatype s dd ∧
        __smtx_value_canonical v = true ∧ minSize ≤ sizeOf v :=
  oracle_all minSize s dd hInh hRec hInfinite

end Smtm
