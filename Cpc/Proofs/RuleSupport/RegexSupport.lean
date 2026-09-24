module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace RuleProofs

def nativeListInRe : List native_Char -> SmtRegLan -> native_Bool
  | [], r => native_re_nullable r
  | c :: cs, r => nativeListInRe cs (native_re_deriv (SmtValue.Char c) r)

@[simp] theorem native_re_str_valid_string (str : native_String) :
    Smtm.native_re_str_valid (impl_native_string_to_values str) =
      native_string_valid str := by
  induction str with
  | nil => rfl
  | cons c cs ih =>
      change
        (native_char_valid c &&
          Smtm.native_re_str_valid (impl_native_string_to_values cs)) =
        (native_char_valid c && native_string_valid cs)
      rw [ih]

/-- String-specialized proof view of regular-language membership. -/
def native_str_in_re (str : native_String) (r : SmtRegLan) : native_Bool :=
  native_string_valid str && nativeListInRe str r

theorem nativeListInRe_eq_model_fold
    (str : native_String) (r : SmtRegLan) :
    nativeListInRe str r =
      native_re_nullable
        ((impl_native_string_to_values str).foldl
          (fun acc c => Smtm.native_re_deriv c acc) r) := by
  induction str generalizing r with
  | nil => rfl
  | cons c cs ih =>
      simp only [nativeListInRe, impl_native_string_to_values, List.map_cons,
        List.foldl_cons]
      exact ih (Smtm.native_re_deriv (SmtValue.Char c) r)

theorem native_str_in_re_eq_model
    (str : native_String) (r : SmtRegLan) :
    native_str_in_re str r =
      Smtm.native_str_in_re (impl_native_string_to_values str) r := by
  cases hValid : native_string_valid str <;>
    simp [native_str_in_re, Smtm.native_str_in_re,
      native_re_str_valid_string, hValid, nativeListInRe_eq_model_fold]

theorem nativeListInRe_empty :
    (xs : List native_Char) -> nativeListInRe xs SmtRegLan.empty = false
  | [] => by rfl
  | _ :: xs => by
      exact nativeListInRe_empty xs

theorem native_re_nullable_mk_union (r s : SmtRegLan) :
    native_re_nullable (native_re_mk_union r s) =
      (native_re_nullable r || native_re_nullable s) := by
  cases r <;> cases s <;>
    simp [native_re_mk_union, native_re_union, native_re_nullable]
  all_goals
    split <;> simp_all [native_re_nullable]

private theorem native_re_mk_union_self (r : SmtRegLan) :
    native_re_mk_union r r = r := by
  cases r <;> simp [native_re_mk_union, native_re_union]

private theorem native_re_mk_union_eq_union_of_ne
    (r s : SmtRegLan) :
    r ≠ SmtRegLan.empty ->
    s ≠ SmtRegLan.empty ->
    r ≠ s ->
    native_re_mk_union r s = SmtRegLan.union r s := by
  intro hr hs hrs
  cases r <;> cases s <;>
    simp [native_re_mk_union, native_re_union] at hr hs ⊢
  all_goals
    try exact False.elim (hrs rfl)
    try
      intro h
      subst h
      exact False.elim (hrs rfl)
    try
      intro h1 h2
      subst h1
      subst h2
      exact False.elim (hrs rfl)

theorem nativeListInRe_mk_union :
    (xs : List native_Char) -> (r s : SmtRegLan) ->
      nativeListInRe xs (native_re_mk_union r s) =
        (nativeListInRe xs r || nativeListInRe xs s)
  | [], r, s => by
      simp [nativeListInRe, native_re_nullable_mk_union]
  | c :: cs, r, s => by
      by_cases hr : r = SmtRegLan.empty
      · subst r
        simp [native_re_mk_union, native_re_union, nativeListInRe_empty]
      · by_cases hs : s = SmtRegLan.empty
        · subst s
          simp [native_re_mk_union, native_re_union, nativeListInRe_empty]
        · by_cases hEq : r = s
          · subst s
            rw [native_re_mk_union_self]
            simp [nativeListInRe]
          · rw [native_re_mk_union_eq_union_of_ne r s hr hs hEq]
            simp [nativeListInRe, native_re_deriv]
            exact nativeListInRe_mk_union cs
              (native_re_deriv c r) (native_re_deriv c s)

theorem native_re_mk_inter_self (r : SmtRegLan) :
    native_re_mk_inter r r = r := by
  cases r <;> simp [native_re_mk_inter, native_re_inter]

private theorem native_re_mk_inter_eq_inter_of_ne
    (r s : SmtRegLan) :
    r ≠ SmtRegLan.empty ->
    s ≠ SmtRegLan.empty ->
    r ≠ s ->
    native_re_mk_inter r s = SmtRegLan.inter r s := by
  intro hr hs hrs
  cases r <;> cases s <;>
    simp [native_re_mk_inter, native_re_inter] at hr hs ⊢
  all_goals
    try exact False.elim (hrs rfl)
    try
      intro h
      subst h
      exact False.elim (hrs rfl)
    try
      intro h1 h2
      subst h1
      subst h2
      exact False.elim (hrs rfl)

theorem native_re_nullable_mk_inter (r s : SmtRegLan) :
    native_re_nullable (native_re_mk_inter r s) =
      (native_re_nullable r && native_re_nullable s) := by
  cases r <;> cases s <;>
    simp [native_re_mk_inter, native_re_inter, native_re_nullable]
  all_goals
    split <;> simp_all [native_re_nullable]

theorem nativeListInRe_mk_inter :
    (xs : List native_Char) -> (r s : SmtRegLan) ->
      nativeListInRe xs (native_re_mk_inter r s) =
        (nativeListInRe xs r && nativeListInRe xs s)
  | [], r, s => by
      simp [nativeListInRe, native_re_nullable_mk_inter]
  | c :: cs, r, s => by
      by_cases hr : r = SmtRegLan.empty
      · subst r
        simp [native_re_mk_inter, native_re_inter, nativeListInRe_empty]
      · by_cases hs : s = SmtRegLan.empty
        · subst s
          simp [native_re_mk_inter, native_re_inter, nativeListInRe_empty]
        · by_cases hEq : r = s
          · subst s
            rw [native_re_mk_inter_self]
            simp [nativeListInRe]
          · rw [native_re_mk_inter_eq_inter_of_ne r s hr hs hEq]
            simp [nativeListInRe, native_re_deriv]
            exact nativeListInRe_mk_inter cs
              (native_re_deriv c r) (native_re_deriv c s)

theorem native_re_nullable_mk_concat (r s : SmtRegLan) :
    native_re_nullable (native_re_mk_concat r s) =
      (native_re_nullable r && native_re_nullable s) := by
  cases r <;> cases s <;>
    simp [native_re_mk_concat, native_re_concat, native_re_nullable]

theorem nativeListInRe_mk_concat_empty_left
    (xs : List native_Char) (r : SmtRegLan) :
    nativeListInRe xs (native_re_mk_concat SmtRegLan.empty r) = false := by
  simp [native_re_mk_concat, native_re_concat, nativeListInRe_empty]

theorem nativeListInRe_mk_concat_empty_right
    (xs : List native_Char) (r : SmtRegLan) :
    nativeListInRe xs (native_re_mk_concat r SmtRegLan.empty) = false := by
  cases r <;> simp [native_re_mk_concat, native_re_concat, nativeListInRe_empty]

theorem nativeListInRe_mk_concat_epsilon_left
    (xs : List native_Char) (r : SmtRegLan) :
    nativeListInRe xs (native_re_mk_concat SmtRegLan.epsilon r) =
      nativeListInRe xs r := by
  cases r <;> simp [native_re_mk_concat, native_re_concat, nativeListInRe_empty]

theorem nativeListInRe_mk_concat_epsilon_right
    (xs : List native_Char) (r : SmtRegLan) :
    nativeListInRe xs (native_re_mk_concat r SmtRegLan.epsilon) =
      nativeListInRe xs r := by
  cases r <;> simp [native_re_mk_concat, native_re_concat, nativeListInRe_empty]

private theorem native_re_mk_concat_eq_concat_of_ne
    (r s : SmtRegLan) :
    r ≠ SmtRegLan.empty ->
    s ≠ SmtRegLan.empty ->
    r ≠ SmtRegLan.epsilon ->
    s ≠ SmtRegLan.epsilon ->
    native_re_mk_concat r s = SmtRegLan.concat r s := by
  intro hrEmpty hsEmpty hrEps hsEps
  cases r <;> cases s <;>
    simp [native_re_mk_concat, native_re_concat] at hrEmpty hsEmpty hrEps hsEps ⊢

theorem nativeListInRe_deriv_mk_concat
    (xs : List native_Char) (c : native_Char) (r s : SmtRegLan) :
    nativeListInRe xs (native_re_deriv c (native_re_mk_concat r s)) =
      nativeListInRe xs
        (native_re_mk_union
          (native_re_mk_concat (native_re_deriv c r) s)
          (if native_re_nullable r then native_re_deriv c s else SmtRegLan.empty)) := by
  by_cases hrEmpty : r = SmtRegLan.empty
  · subst r
    simp [native_re_mk_concat, native_re_concat, native_re_deriv, native_re_nullable,
      nativeListInRe_mk_union, nativeListInRe_empty]
  · by_cases hsEmpty : s = SmtRegLan.empty
    · subst s
      have hL :
          nativeListInRe xs
            (native_re_deriv c (native_re_mk_concat r SmtRegLan.empty)) =
            false := by
        simp [native_re_mk_concat, native_re_concat, native_re_deriv, nativeListInRe_empty]
      rw [hL]
      rw [nativeListInRe_mk_union]
      rw [nativeListInRe_mk_concat_empty_right]
      simp [native_re_deriv, nativeListInRe_empty]
    · by_cases hrEps : r = SmtRegLan.epsilon
      · subst r
        simp [native_re_mk_concat, native_re_concat, native_re_deriv, native_re_nullable,
          nativeListInRe_mk_union, nativeListInRe_empty]
      · by_cases hsEps : s = SmtRegLan.epsilon
        · subst s
          have hMk : native_re_mk_concat r SmtRegLan.epsilon = r := by
            cases r <;> simp [native_re_mk_concat, native_re_concat] at hrEmpty hrEps ⊢
          rw [hMk]
          rw [nativeListInRe_mk_union]
          rw [nativeListInRe_mk_concat_epsilon_right]
          simp [native_re_deriv, nativeListInRe_empty]
        · have hMk :=
            native_re_mk_concat_eq_concat_of_ne r s hrEmpty hsEmpty hrEps hsEps
          rw [hMk]
          change
            nativeListInRe xs
                (native_re_mk_union
                  (native_re_mk_concat (native_re_deriv c r) s)
                  (if native_re_nullable r then native_re_deriv c s
                    else SmtRegLan.empty)) = _
          simp [nativeListInRe_mk_union]

def nativeListInReConcat :
    List native_Char -> SmtRegLan -> SmtRegLan -> native_Bool
  | [], r, s => native_re_nullable r && native_re_nullable s
  | c :: cs, r, s =>
      (native_re_nullable r && nativeListInRe (c :: cs) s) ||
        nativeListInReConcat cs (native_re_deriv c r) s

theorem nativeListInRe_mk_concat :
    (xs : List native_Char) -> (r s : SmtRegLan) ->
      nativeListInRe xs (native_re_mk_concat r s) =
        nativeListInReConcat xs r s
  | [], r, s => by
      simp [nativeListInRe, nativeListInReConcat,
        native_re_nullable_mk_concat]
  | c :: cs, r, s => by
      change
        nativeListInRe cs
            (native_re_deriv c (native_re_mk_concat r s)) =
          ((native_re_nullable r &&
              nativeListInRe cs (native_re_deriv c s)) ||
            nativeListInReConcat cs (native_re_deriv c r) s)
      rw [nativeListInRe_deriv_mk_concat cs c r s]
      rw [nativeListInRe_mk_union]
      rw [nativeListInRe_mk_concat cs (native_re_deriv c r) s]
      cases hNullable : native_re_nullable r <;>
        simp [nativeListInRe_empty, Bool.or_comm]

theorem nativeListInReConcat_true_iff_exists_append :
    (xs : List native_Char) -> (r s : SmtRegLan) ->
      nativeListInReConcat xs r s = true ↔
        ∃ xs₁ xs₂ : List native_Char,
          xs₁ ++ xs₂ = xs ∧
            nativeListInRe xs₁ r = true ∧
            nativeListInRe xs₂ s = true
  | [], r, s => by
      constructor
      · intro h
        simp [nativeListInReConcat, Bool.and_eq_true] at h
        exact ⟨[], [], by rfl, by simpa [nativeListInRe] using h.1,
          by simpa [nativeListInRe] using h.2⟩
      · intro h
        rcases h with ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
        cases xs₁ with
        | nil =>
            cases xs₂ with
            | nil =>
                simp [nativeListInReConcat, nativeListInRe] at hLeft hRight ⊢
                simp [hLeft, hRight]
            | cons _ _ =>
                simp at hAppend
        | cons _ _ =>
            simp at hAppend
  | c :: cs, r, s => by
      constructor
      · intro h
        simp [nativeListInReConcat, Bool.or_eq_true, Bool.and_eq_true] at h
        rcases h with hHead | hTail
        · exact ⟨[], c :: cs, by rfl,
            by simpa [nativeListInRe] using hHead.1, hHead.2⟩
        · have hTailExists :=
            (nativeListInReConcat_true_iff_exists_append cs
              (native_re_deriv c r) s).1 hTail
          rcases hTailExists with ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
          exact ⟨c :: xs₁, xs₂, by simp [hAppend],
            by simpa [nativeListInRe] using hLeft, hRight⟩
      · intro h
        rcases h with ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
        cases xs₁ with
        | nil =>
            cases xs₂ with
            | nil =>
                simp at hAppend
            | cons _ _ =>
                cases hAppend
                have hNullable : native_re_nullable r = true := by
                  simpa [nativeListInRe] using hLeft
                simp [nativeListInReConcat,
                  hNullable, hRight]
        | cons _ ds =>
            cases hAppend
            have hLeftDeriv :
                nativeListInRe ds (native_re_deriv c r) = true := by
              simpa [nativeListInRe] using hLeft
            have hTail :
                nativeListInReConcat (ds ++ xs₂) (native_re_deriv c r) s =
                  true :=
              (nativeListInReConcat_true_iff_exists_append (ds ++ xs₂)
                (native_re_deriv c r) s).2
                ⟨ds, xs₂, by rfl, hLeftDeriv, hRight⟩
            simp [nativeListInReConcat, hTail]

theorem nativeListInRe_mk_concat_true_iff_exists_append
    (xs : List native_Char) (r s : SmtRegLan) :
    nativeListInRe xs (native_re_mk_concat r s) = true ↔
      ∃ xs₁ xs₂ : List native_Char,
        xs₁ ++ xs₂ = xs ∧
          nativeListInRe xs₁ r = true ∧
          nativeListInRe xs₂ s = true := by
  rw [nativeListInRe_mk_concat xs r s]
  exact nativeListInReConcat_true_iff_exists_append xs r s

theorem native_str_in_re_mk_inter
    (str : native_String) (r s : SmtRegLan) :
    native_str_in_re str (native_re_mk_inter r s) =
      (native_str_in_re str r && native_str_in_re str s) := by
  by_cases hValid : native_string_valid str = true
  · simpa [native_str_in_re, hValid, nativeListInRe] using
      nativeListInRe_mk_inter str r s
  · have hInvalid : native_string_valid str = false := by
      cases h : native_string_valid str <;> simp [h] at hValid ⊢
    simp [native_str_in_re, hInvalid]

theorem native_str_in_re_re_inter
    (str : native_String) (r s : SmtRegLan) :
    native_str_in_re str (native_re_inter r s) =
      (native_str_in_re str r && native_str_in_re str s) := by
  simpa [native_re_mk_inter] using native_str_in_re_mk_inter str r s

theorem nativeListInRe_mk_comp :
    ∀ (xs : List native_Char) (r : SmtRegLan),
      nativeListInRe xs (native_re_mk_comp r) =
        Bool.not (nativeListInRe xs r)
  | [], r => by
      cases r <;>
        simp [nativeListInRe, native_re_mk_comp, native_re_comp,
          native_re_nullable]
  | c :: cs, r => by
      cases r <;>
        simp only [nativeListInRe, native_re_mk_comp, native_re_comp,
          native_re_deriv]
      case comp r =>
        let d := native_re_deriv (SmtValue.Char c) r
        change nativeListInRe cs d =
          Bool.not (nativeListInRe cs (native_re_mk_comp d))
        have h := nativeListInRe_mk_comp cs d
        cases hA : nativeListInRe cs d <;>
          cases hB : nativeListInRe cs (native_re_mk_comp d) <;>
          simp [hA, hB] at h ⊢
      case empty =>
        exact nativeListInRe_mk_comp cs SmtRegLan.empty
      case epsilon =>
        exact nativeListInRe_mk_comp cs SmtRegLan.empty
      all_goals
        simpa [native_re_mk_comp, native_re_comp] using
          nativeListInRe_mk_comp cs _

theorem native_str_in_re_re_comp
    (str : native_String) (r : SmtRegLan) :
    native_str_in_re str (native_re_comp r) =
      (native_string_valid str && Bool.not (native_str_in_re str r)) := by
  change native_str_in_re str (native_re_mk_comp r) = _
  cases hValid : native_string_valid str with
  | false => simp [native_str_in_re, hValid]
  | true =>
      simp only [native_str_in_re, hValid,
        Bool.true_and]
      exact nativeListInRe_mk_comp str r

theorem native_str_in_re_mk_comp
    (str : native_String) (r : SmtRegLan) :
    native_str_in_re str (native_re_mk_comp r) =
      (native_string_valid str && Bool.not (native_str_in_re str r)) := by
  simpa [native_re_mk_comp] using native_str_in_re_re_comp str r

theorem native_str_in_re_re_concat_intro
    (s1 s2 : native_String) (r1 r2 : SmtRegLan) :
    native_str_in_re s1 r1 = true ->
    native_str_in_re s2 r2 = true ->
    native_str_in_re (s1 ++ s2) (native_re_concat r1 r2) = true := by
  intro h1 h2
  have h1Parts :
      native_string_valid s1 = true ∧ nativeListInRe s1 r1 = true := by
    simpa [native_str_in_re, nativeListInRe] using h1
  have h2Parts :
      native_string_valid s2 = true ∧ nativeListInRe s2 r2 = true := by
    simpa [native_str_in_re, nativeListInRe] using h2
  have hValidAppend : native_string_valid (s1 ++ s2) = true := by
    have hAll1 : s1.all native_char_valid = true := by
      simpa [native_string_valid] using h1Parts.1
    have hAll2 : s2.all native_char_valid = true := by
      simpa [native_string_valid] using h2Parts.1
    change (s1 ++ s2).all native_char_valid = true
    simp [hAll1, hAll2]
  have h := (nativeListInRe_mk_concat_true_iff_exists_append
    (s1 ++ s2) r1 r2).2
    ⟨s1, s2, by simp, h1Parts.2, h2Parts.2⟩
  change native_str_in_re (s1 ++ s2) (native_re_mk_concat r1 r2) = true
  simpa [native_str_in_re, hValidAppend, nativeListInRe] using h

theorem nativeListInRe_mk_concat_congr
    (xs : List native_Char) (r r' s s' : SmtRegLan)
    (hr : ∀ ys : List native_Char, nativeListInRe ys r = nativeListInRe ys r')
    (hs : ∀ ys : List native_Char, nativeListInRe ys s = nativeListInRe ys s') :
    nativeListInRe xs (native_re_mk_concat r s) =
      nativeListInRe xs (native_re_mk_concat r' s') := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    rcases
      (nativeListInRe_mk_concat_true_iff_exists_append xs r s).1 h
        with ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
    apply (nativeListInRe_mk_concat_true_iff_exists_append xs r' s').2
    refine ⟨xs₁, xs₂, hAppend, ?_, ?_⟩
    · rwa [← hr xs₁]
    · rwa [← hs xs₂]
  · intro h
    rcases
      (nativeListInRe_mk_concat_true_iff_exists_append xs r' s').1 h
        with ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
    apply (nativeListInRe_mk_concat_true_iff_exists_append xs r s).2
    refine ⟨xs₁, xs₂, hAppend, ?_, ?_⟩
    · rwa [hr xs₁]
    · rwa [hs xs₂]

theorem nativeListInRe_mk_concat_assoc
    (xs : List native_Char) (r s t : SmtRegLan) :
    nativeListInRe xs (native_re_mk_concat (native_re_mk_concat r s) t) =
      nativeListInRe xs (native_re_mk_concat r (native_re_mk_concat s t)) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    rcases (nativeListInRe_mk_concat_true_iff_exists_append xs
        (native_re_mk_concat r s) t).1 h with
      ⟨xrs, xt, hAppend, hrs, ht⟩
    rcases (nativeListInRe_mk_concat_true_iff_exists_append xrs r s).1 hrs with
      ⟨xr, xs', hAppendRS, hr, hs⟩
    apply (nativeListInRe_mk_concat_true_iff_exists_append xs r
      (native_re_mk_concat s t)).2
    refine ⟨xr, xs' ++ xt, ?_, hr, ?_⟩
    · rw [← List.append_assoc, hAppendRS, hAppend]
    · exact (nativeListInRe_mk_concat_true_iff_exists_append (xs' ++ xt) s t).2
        ⟨xs', xt, rfl, hs, ht⟩
  · intro h
    rcases (nativeListInRe_mk_concat_true_iff_exists_append xs r
        (native_re_mk_concat s t)).1 h with
      ⟨xr, xst, hAppend, hr, hst⟩
    rcases (nativeListInRe_mk_concat_true_iff_exists_append xst s t).1 hst with
      ⟨xs', xt, hAppendST, hs, ht⟩
    apply (nativeListInRe_mk_concat_true_iff_exists_append xs
      (native_re_mk_concat r s) t).2
    refine ⟨xr ++ xs', xt, ?_, ?_, ht⟩
    · rw [List.append_assoc, hAppendST, hAppend]
    · exact (nativeListInRe_mk_concat_true_iff_exists_append (xr ++ xs') r s).2
        ⟨xr, xs', rfl, hr, hs⟩

theorem nativeListInRe_char_true_length
    (xs : List native_Char) (c : SmtValue)
    (h : nativeListInRe xs (SmtRegLan.char c) = true) :
    xs.length = 1 := by
  cases xs with
  | nil => simp [nativeListInRe, native_re_nullable] at h
  | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y ys =>
          have hFalse :
              nativeListInRe (x :: y :: ys) (SmtRegLan.char c) = false := by
            simp [nativeListInRe, native_re_deriv]
            split <;> simp [native_re_deriv, nativeListInRe_empty]
          rw [hFalse] at h
          simp at h

theorem nativeListInRe_range_true_length
    (xs : List native_Char) (lo hi : SmtValue)
    (h : nativeListInRe xs (SmtRegLan.range lo hi) = true) :
    xs.length = 1 := by
  cases xs with
  | nil => simp [nativeListInRe, native_re_nullable] at h
  | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y ys =>
          have hFalse :
              nativeListInRe (x :: y :: ys) (SmtRegLan.range lo hi) = false := by
            simp [nativeListInRe, native_re_deriv]
            split <;> simp [native_re_deriv, nativeListInRe_empty]
          rw [hFalse] at h
          simp at h

theorem nativeListInRe_re_range_true_length
    (xs : List native_Char) (lo hi : List SmtValue)
    (h : nativeListInRe xs (native_re_range lo hi) = true) :
    xs.length = 1 := by
  cases lo with
  | nil => simp [native_re_range, nativeListInRe_empty] at h
  | cons lo loTail =>
      cases loTail with
      | nil =>
          cases hi with
          | nil => simp [native_re_range, nativeListInRe_empty] at h
          | cons hi hiTail =>
              cases hiTail with
              | nil => exact nativeListInRe_range_true_length xs lo hi h
              | cons _ _ => simp [native_re_range, nativeListInRe_empty] at h
      | cons _ _ => simp [native_re_range, nativeListInRe_empty] at h

theorem nativeListInRe_re_of_string_true_length :
    (pat xs : List native_Char) ->
      nativeListInRe xs (impl_native_re_of_list (impl_native_string_to_values pat)) = true ->
      xs.length = pat.length
  | [], xs, h => by
      cases xs with
      | nil => rfl
      | cons c cs =>
          have hFalse : nativeListInRe (c :: cs)
              (impl_native_re_of_list (impl_native_string_to_values [])) = false := by
            change nativeListInRe cs SmtRegLan.empty = false
            exact nativeListInRe_empty cs
          rw [hFalse] at h
          simp at h
  | c :: pat, xs, h => by
      rcases (nativeListInRe_mk_concat_true_iff_exists_append xs
          (SmtRegLan.char (SmtValue.Char c))
          (impl_native_re_of_list (impl_native_string_to_values pat))).1
          (by
            change nativeListInRe xs
              (native_re_mk_concat (SmtRegLan.char (SmtValue.Char c))
                (impl_native_re_of_list (impl_native_string_to_values pat))) = true at h
            exact h) with
        ⟨left, right, hAppend, hLeft, hRight⟩
      have hLeftLen : left.length = 1 :=
        nativeListInRe_char_true_length left (SmtValue.Char c) hLeft
      have hRightLen : right.length = pat.length :=
        nativeListInRe_re_of_string_true_length pat right hRight
      rw [← hAppend]
      simp [hLeftLen, hRightLen, Nat.add_comm]

theorem nativeListInRe_str_to_re_string_true_length
    (pat xs : List native_Char)
    (h : nativeListInRe xs
      (native_str_to_re (impl_native_string_to_values pat)) = true) :
    xs.length = pat.length := by
  simpa [native_str_to_re] using
    nativeListInRe_re_of_string_true_length pat xs h

theorem nativeListInRe_allchar_true_iff (xs : List native_Char) :
    nativeListInRe xs native_re_allchar = true ↔
      xs.length = 1 ∧ xs.all native_char_valid = true := by
  cases xs with
  | nil =>
      simp [nativeListInRe, native_re_allchar, native_re_nullable]
  | cons c xs =>
      cases xs with
      | nil =>
          cases hValid : native_char_valid c <;>
            simp [nativeListInRe, native_re_allchar, native_re_deriv,
              native_re_elem_valid, native_re_nullable, hValid]
      | cons d ds =>
          have hEmpty := nativeListInRe_empty ds
          cases hValid : native_char_valid c <;>
            simpa [nativeListInRe, native_re_allchar, native_re_deriv,
              native_re_elem_valid, hValid] using hEmpty

private theorem native_re_deriv_re_all
    (c : native_Char) (hValid : native_char_valid c = true) :
    native_re_deriv c native_re_all = native_re_all := by
  simp [native_re_all, native_re_deriv, native_re_elem_valid,
    native_re_concat, hValid]

private theorem native_re_deriv_re_all_invalid
    (c : native_Char) (hValid : native_char_valid c = false) :
    native_re_deriv c native_re_all = SmtRegLan.empty := by
  simp [native_re_all, native_re_deriv, native_re_elem_valid,
    native_re_concat, hValid]

theorem nativeListInRe_re_all_true_iff (xs : List native_Char) :
    nativeListInRe xs native_re_all = true ↔
      xs.all native_char_valid = true := by
  induction xs with
  | nil =>
      simp [nativeListInRe, native_re_all, native_re_nullable]
  | cons c xs ih =>
      cases hValid : native_char_valid c
      · simpa [nativeListInRe, native_re_deriv_re_all_invalid c hValid,
          hValid] using nativeListInRe_empty xs
      · simpa [nativeListInRe, native_re_deriv_re_all c hValid, hValid,
          List.all_eq_true] using ih

theorem nativeListInRe_re_all
    (xs : List native_Char) (hValid : xs.all native_char_valid = true) :
    nativeListInRe xs native_re_all = true := by
  exact (nativeListInRe_re_all_true_iff xs).2 hValid

theorem native_str_in_re_re_all (str : native_String)
    (hValid : native_string_valid str = true) :
    native_str_in_re str native_re_all = true := by
  have hListValid : str.all native_char_valid = true := by
    simpa [native_string_valid] using hValid
  simpa [native_str_in_re, hValid, nativeListInRe] using
    nativeListInRe_re_all str hListValid

def nativeSigmaExact : Nat -> SmtRegLan
  | 0 => SmtRegLan.epsilon
  | n + 1 => native_re_mk_concat (nativeSigmaExact n) native_re_allchar

def nativeSigmaAtLeast : Nat -> SmtRegLan
  | 0 => native_re_all
  | n + 1 => native_re_mk_concat (nativeSigmaAtLeast n) native_re_allchar

theorem nativeListInRe_sigmaExact_true_iff :
    (n : Nat) -> (xs : List native_Char) ->
      nativeListInRe xs (nativeSigmaExact n) = true ↔
        xs.length = n ∧ xs.all native_char_valid = true
  | 0, xs => by
      cases xs with
      | nil =>
          simp [nativeSigmaExact, nativeListInRe, native_re_nullable]
      | cons c cs =>
          simpa [nativeSigmaExact, nativeListInRe, native_re_nullable,
            native_re_deriv] using nativeListInRe_empty cs
  | n + 1, xs => by
      constructor
      · intro h
        rcases (nativeListInRe_mk_concat_true_iff_exists_append xs
            (nativeSigmaExact n) native_re_allchar).1
            (by simpa [nativeSigmaExact] using h) with
          ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
        have hLeftParts :
            xs₁.length = n ∧ xs₁.all native_char_valid = true :=
          (nativeListInRe_sigmaExact_true_iff n xs₁).1 hLeft
        have hRightParts :
            xs₂.length = 1 ∧ xs₂.all native_char_valid = true :=
          (nativeListInRe_allchar_true_iff xs₂).1 hRight
        have hLen := congrArg List.length hAppend
        simp [hLeftParts.1, hRightParts.1] at hLen
        have hValid : xs.all native_char_valid = true := by
          rw [← hAppend, List.all_append]
          simp [hLeftParts.2, hRightParts.2]
        exact ⟨by omega, hValid⟩
      · intro hParts
        rcases hParts with ⟨hLen, hValid⟩
        let xs₁ := xs.take n
        let xs₂ := xs.drop n
        have hLeftLen : xs₁.length = n := by
          simp [xs₁]
          omega
        have hRightLen : xs₂.length = 1 := by
          simp [xs₂]
          omega
        have hAppend : xs₁ ++ xs₂ = xs := by
          simp [xs₁, xs₂]
        have hValidAppend : (xs₁ ++ xs₂).all native_char_valid = true := by
          simpa [hAppend] using hValid
        rw [List.all_append] at hValidAppend
        have hValidParts :
            xs₁.all native_char_valid = true ∧
              xs₂.all native_char_valid = true := by
          simpa [Bool.and_eq_true] using hValidAppend
        have hLeftValid : xs₁.all native_char_valid = true :=
          hValidParts.1
        have hRightValid : xs₂.all native_char_valid = true :=
          hValidParts.2
        have hLeft :
            nativeListInRe xs₁ (nativeSigmaExact n) = true :=
          (nativeListInRe_sigmaExact_true_iff n xs₁).2
            ⟨hLeftLen, hLeftValid⟩
        have hRight :
            nativeListInRe xs₂ native_re_allchar = true :=
          (nativeListInRe_allchar_true_iff xs₂).2
            ⟨hRightLen, hRightValid⟩
        have hConcat :
            nativeListInRe xs
                (native_re_mk_concat (nativeSigmaExact n) native_re_allchar) =
              true :=
          (nativeListInRe_mk_concat_true_iff_exists_append xs
            (nativeSigmaExact n) native_re_allchar).2
            ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
        simpa [nativeSigmaExact] using hConcat

theorem nativeListInRe_sigmaAtLeast_true_iff :
    (n : Nat) -> (xs : List native_Char) ->
      nativeListInRe xs (nativeSigmaAtLeast n) = true ↔
        n ≤ xs.length ∧ xs.all native_char_valid = true
  | 0, xs => by
      constructor
      · intro h
        exact ⟨by omega, (nativeListInRe_re_all_true_iff xs).1 h⟩
      · intro hParts
        exact nativeListInRe_re_all xs hParts.2
  | n + 1, xs => by
      constructor
      · intro h
        rcases (nativeListInRe_mk_concat_true_iff_exists_append xs
            (nativeSigmaAtLeast n) native_re_allchar).1
            (by simpa [nativeSigmaAtLeast] using h) with
          ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
        have hLeftParts :
            n ≤ xs₁.length ∧ xs₁.all native_char_valid = true :=
          (nativeListInRe_sigmaAtLeast_true_iff n xs₁).1 hLeft
        have hRightParts :
            xs₂.length = 1 ∧ xs₂.all native_char_valid = true :=
          (nativeListInRe_allchar_true_iff xs₂).1 hRight
        have hLen := congrArg List.length hAppend
        simp [hRightParts.1] at hLen
        have hValid : xs.all native_char_valid = true := by
          rw [← hAppend, List.all_append]
          simp [hLeftParts.2, hRightParts.2]
        exact ⟨by omega, hValid⟩
      · intro hParts
        rcases hParts with ⟨hLen, hValid⟩
        let cut := xs.length - 1
        let xs₁ := xs.take cut
        let xs₂ := xs.drop cut
        have hLeftLen : n ≤ xs₁.length := by
          simp [xs₁, cut]
          omega
        have hRightLen : xs₂.length = 1 := by
          simp [xs₂, cut]
          omega
        have hAppend : xs₁ ++ xs₂ = xs := by
          simp [xs₁, xs₂]
        have hValidAppend : (xs₁ ++ xs₂).all native_char_valid = true := by
          simpa [hAppend] using hValid
        rw [List.all_append] at hValidAppend
        have hValidParts :
            xs₁.all native_char_valid = true ∧
              xs₂.all native_char_valid = true := by
          simpa [Bool.and_eq_true] using hValidAppend
        have hLeftValid : xs₁.all native_char_valid = true :=
          hValidParts.1
        have hRightValid : xs₂.all native_char_valid = true :=
          hValidParts.2
        have hLeft :
            nativeListInRe xs₁ (nativeSigmaAtLeast n) = true :=
          (nativeListInRe_sigmaAtLeast_true_iff n xs₁).2
            ⟨hLeftLen, hLeftValid⟩
        have hRight :
            nativeListInRe xs₂ native_re_allchar = true :=
          (nativeListInRe_allchar_true_iff xs₂).2
            ⟨hRightLen, hRightValid⟩
        have hConcat :
            nativeListInRe xs
                (native_re_mk_concat (nativeSigmaAtLeast n) native_re_allchar) =
              true :=
          (nativeListInRe_mk_concat_true_iff_exists_append xs
            (nativeSigmaAtLeast n) native_re_allchar).2
            ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
        simpa [nativeSigmaAtLeast] using hConcat

theorem nativeListInRe_exact_concat_re_all_true_iff
    (n : Nat) (xs : List native_Char) :
    nativeListInRe xs (native_re_mk_concat (nativeSigmaExact n) native_re_all) = true ↔
      n ≤ xs.length ∧ xs.all native_char_valid = true := by
  constructor
  · intro h
    rcases (nativeListInRe_mk_concat_true_iff_exists_append xs
        (nativeSigmaExact n) native_re_all).1 h with
      ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
    have hLeftParts :
        xs₁.length = n ∧ xs₁.all native_char_valid = true :=
      (nativeListInRe_sigmaExact_true_iff n xs₁).1 hLeft
    have hRightValid : xs₂.all native_char_valid = true :=
      (nativeListInRe_re_all_true_iff xs₂).1 hRight
    have hLen := congrArg List.length hAppend
    simp [hLeftParts.1] at hLen
    have hValid : xs.all native_char_valid = true := by
      rw [← hAppend, List.all_append]
      simp [hLeftParts.2, hRightValid]
    exact ⟨by omega, hValid⟩
  · intro hParts
    rcases hParts with ⟨hLen, hValid⟩
    let k := xs.length - n
    let xs₁ := xs.take n
    let xs₂ := xs.drop n
    have hLeftLen : xs₁.length = n := by
      simp [xs₁]
      omega
    have hAppend : xs₁ ++ xs₂ = xs := by
      simp [xs₁, xs₂]
    have hValidAppend : (xs₁ ++ xs₂).all native_char_valid = true := by
      simpa [hAppend] using hValid
    rw [List.all_append] at hValidAppend
    have hValidParts :
        xs₁.all native_char_valid = true ∧
          xs₂.all native_char_valid = true := by
      simpa [Bool.and_eq_true] using hValidAppend
    have hLeftValid : xs₁.all native_char_valid = true :=
      hValidParts.1
    have hRightValid : xs₂.all native_char_valid = true :=
      hValidParts.2
    have hLeft : nativeListInRe xs₁ (nativeSigmaExact n) = true :=
      (nativeListInRe_sigmaExact_true_iff n xs₁).2
        ⟨hLeftLen, hLeftValid⟩
    have hRight : nativeListInRe xs₂ native_re_all = true :=
      nativeListInRe_re_all xs₂ hRightValid
    exact (nativeListInRe_mk_concat_true_iff_exists_append xs
      (nativeSigmaExact n) native_re_all).2
      ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩

theorem nativeListInRe_exact_concat_re_all_eq_atLeast
    (n : Nat) (xs : List native_Char) :
    nativeListInRe xs (native_re_mk_concat (nativeSigmaExact n) native_re_all) =
      nativeListInRe xs (nativeSigmaAtLeast n) := by
  apply Bool.eq_iff_iff.mpr
  rw [nativeListInRe_exact_concat_re_all_true_iff,
    nativeListInRe_sigmaAtLeast_true_iff]

theorem nativeListInRe_atLeast_concat_re_all_eq_atLeast
    (n : Nat) (xs : List native_Char) :
    nativeListInRe xs (native_re_mk_concat (nativeSigmaAtLeast n) native_re_all) =
      nativeListInRe xs (nativeSigmaAtLeast n) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    rcases (nativeListInRe_mk_concat_true_iff_exists_append xs
        (nativeSigmaAtLeast n) native_re_all).1 h with
      ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
    have hLeftParts :
        n ≤ xs₁.length ∧ xs₁.all native_char_valid = true :=
      (nativeListInRe_sigmaAtLeast_true_iff n xs₁).1 hLeft
    have hRightValid : xs₂.all native_char_valid = true :=
      (nativeListInRe_re_all_true_iff xs₂).1 hRight
    apply (nativeListInRe_sigmaAtLeast_true_iff n xs).2
    have hLen := congrArg List.length hAppend
    simp at hLen
    have hValid : xs.all native_char_valid = true := by
      rw [← hAppend, List.all_append]
      simp [hLeftParts.2, hRightValid]
    exact ⟨by omega, hValid⟩
  · intro h
    have hNilAll : nativeListInRe [] native_re_all = true :=
      nativeListInRe_re_all [] (by simp)
    exact (nativeListInRe_mk_concat_true_iff_exists_append xs
      (nativeSigmaAtLeast n) native_re_all).2
      ⟨xs, [], by simp, h, hNilAll⟩

end RuleProofs
