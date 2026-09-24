module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private def nativeRePow : native_Nat -> SmtRegLan -> SmtRegLan
  | 0, _ => SmtRegLan.epsilon
  | Nat.succ n, r => native_re_concat r (nativeRePow n r)

def nativeReExpRec : native_Nat -> SmtRegLan -> SmtRegLan
  | 0, _ => SmtRegLan.epsilon
  | Nat.succ n, r => native_re_concat (nativeReExpRec n r) r

private theorem model_eval_re_exp_rec_reglan_eq :
    ∀ n r,
      __smtx_re_exp_rec n (SmtValue.RegLan r) =
        SmtValue.RegLan (nativeReExpRec n r) := by
  intro n
  induction n with
  | zero =>
      intro r
      rfl
  | succ n ih =>
      intro r
      simp [__smtx_re_exp_rec, nativeReExpRec, ih,
        __smtx_model_eval_re_concat]


theorem native_re_concat_right_epsilon (r : SmtRegLan) :
    native_re_concat r SmtRegLan.epsilon = r := by
  cases r <;> simp [native_re_concat]

theorem native_re_concat_left_epsilon (r : SmtRegLan) :
    native_re_concat SmtRegLan.epsilon r = r := by
  cases r <;> simp [native_re_concat]

private def nativeListInRe (xs : List native_Char) (r : SmtRegLan) :
    native_Bool :=
  native_re_nullable <| xs.foldl (fun acc c => native_re_deriv c acc) r

private theorem native_re_str_valid_string (str : native_String) :
    native_re_str_valid (impl_native_string_to_values str) =
      native_string_valid str := by
  induction str with
  | nil => rfl
  | cons c cs ih =>
      change
        (native_char_valid c && native_re_str_valid (impl_native_string_to_values cs)) =
          (native_char_valid c && native_string_valid cs)
      rw [ih]

private theorem nativeListInRe_empty :
    (xs : List native_Char) -> nativeListInRe xs SmtRegLan.empty = false
  | [] => by rfl
  | _ :: xs => by
      exact nativeListInRe_empty xs

private theorem native_re_nullable_mk_union (r s : SmtRegLan) :
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

private theorem nativeListInRe_mk_union :
    (xs : List native_Char) -> (r s : SmtRegLan) ->
      nativeListInRe xs (native_re_mk_union r s) =
        (nativeListInRe xs r || nativeListInRe xs s)
  | [], r, s => by
      simp [nativeListInRe, native_re_nullable_mk_union,
        impl_native_string_to_values]
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
            simp [nativeListInRe]
            exact nativeListInRe_mk_union cs
              (native_re_deriv c r) (native_re_deriv c s)

private theorem native_str_in_re_mk_union
    (str : native_String) (r s : SmtRegLan) :
    native_str_in_re str (native_re_mk_union r s) =
      (native_str_in_re str r || native_str_in_re str s) := by
  by_cases hValid : native_string_valid str = true
  · have hValueValid :
        native_re_str_valid (impl_native_string_to_values str) = true := by
      rw [native_re_str_valid_string]
      exact hValid
    simpa [Smtm.native_str_in_re, hValueValid, nativeListInRe] using
      nativeListInRe_mk_union str r s
  · have hInvalid : native_string_valid str = false := by
      cases h : native_string_valid str <;> simp [h] at hValid ⊢
    have hValueInvalid :
        native_re_str_valid (impl_native_string_to_values str) = false := by
      rw [native_re_str_valid_string]
      exact hInvalid
    simp [Smtm.native_str_in_re, hValueInvalid]

private theorem native_str_in_re_re_union
    (str : native_String) (r s : SmtRegLan) :
    native_str_in_re str (native_re_union r s) =
      (native_str_in_re str r || native_str_in_re str s) := by
  exact native_str_in_re_mk_union str r s

private theorem native_str_in_re_empty (str : native_String) :
    native_str_in_re str SmtRegLan.empty = false := by
  by_cases hValid : native_string_valid str = true
  · have hValueValid :
        native_re_str_valid (impl_native_string_to_values str) = true := by
      rw [native_re_str_valid_string]
      exact hValid
    simpa [Smtm.native_str_in_re, hValueValid, nativeListInRe] using
      nativeListInRe_empty str
  · have hInvalid : native_string_valid str = false := by
      cases h : native_string_valid str <;> simp [h] at hValid ⊢
    have hValueInvalid :
        native_re_str_valid (impl_native_string_to_values str) = false := by
      rw [native_re_str_valid_string]
      exact hInvalid
    simp [Smtm.native_str_in_re, hValueInvalid]

private theorem native_str_in_re_re_none (str : native_String) :
    native_str_in_re str native_re_none = false := by
  simpa [native_re_none] using native_str_in_re_empty str

private theorem native_re_nullable_mk_concat (r s : SmtRegLan) :
    native_re_nullable (native_re_mk_concat r s) =
      (native_re_nullable r && native_re_nullable s) := by
  cases r <;> cases s <;>
    simp [native_re_mk_concat, native_re_concat, native_re_nullable]

private theorem nativeListInRe_mk_concat_empty_right
    (xs : List native_Char) (r : SmtRegLan) :
    nativeListInRe xs (native_re_mk_concat r SmtRegLan.empty) = false := by
  cases r <;> simp [native_re_mk_concat, native_re_concat, nativeListInRe_empty]

private theorem nativeListInRe_mk_concat_epsilon_right
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

private theorem nativeListInRe_deriv_mk_concat
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
        simp [native_re_mk_concat, native_re_concat, native_re_deriv,
          nativeListInRe_empty]
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

private def nativeListInReConcat :
    List native_Char -> SmtRegLan -> SmtRegLan -> native_Bool
  | [], r, s => native_re_nullable r && native_re_nullable s
  | c :: cs, r, s =>
      (native_re_nullable r && nativeListInRe (c :: cs) s) ||
        nativeListInReConcat cs (native_re_deriv c r) s

private theorem nativeListInRe_mk_concat :
    (xs : List native_Char) -> (r s : SmtRegLan) ->
      nativeListInRe xs (native_re_mk_concat r s) =
        nativeListInReConcat xs r s
  | [], r, s => by
      simp [nativeListInRe, nativeListInReConcat,
        native_re_nullable_mk_concat, impl_native_string_to_values]
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

private theorem nativeListInReConcat_true_iff_exists_append :
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
        exact ⟨[], [], by rfl,
          by simpa [nativeListInRe, impl_native_string_to_values] using h.1,
          by exact h.2⟩
      · intro h
        rcases h with ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
        cases xs₁ with
        | nil =>
            cases xs₂ with
            | nil =>
                simp [nativeListInReConcat, nativeListInRe,
                  impl_native_string_to_values] at hLeft hRight ⊢
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
            by exact hHead.1, hHead.2⟩
        · have hTailExists :=
            (nativeListInReConcat_true_iff_exists_append cs
              (native_re_deriv c r) s).1 hTail
          rcases hTailExists with ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
          exact ⟨c :: xs₁, xs₂, by simp [hAppend],
            by exact hLeft, hRight⟩
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
                  exact hLeft
                simp [nativeListInReConcat,
                  hNullable, hRight]
        | cons _ ds =>
            cases hAppend
            have hLeftDeriv :
                nativeListInRe ds (native_re_deriv c r) = true := by
              exact hLeft
            have hTail :
                nativeListInReConcat (ds ++ xs₂) (native_re_deriv c r) s =
                  true :=
              (nativeListInReConcat_true_iff_exists_append (ds ++ xs₂)
                (native_re_deriv c r) s).2
                ⟨ds, xs₂, by rfl, hLeftDeriv, hRight⟩
            simp [nativeListInReConcat, hTail]

private theorem nativeListInRe_mk_concat_true_iff_exists_append
    (xs : List native_Char) (r s : SmtRegLan) :
    nativeListInRe xs (native_re_mk_concat r s) = true ↔
      ∃ xs₁ xs₂ : List native_Char,
        xs₁ ++ xs₂ = xs ∧
          nativeListInRe xs₁ r = true ∧
          nativeListInRe xs₂ s = true := by
  rw [nativeListInRe_mk_concat xs r s]
  exact nativeListInReConcat_true_iff_exists_append xs r s

private theorem native_string_valid_append_left
    (xs ys : List native_Char) :
    native_string_valid (xs ++ ys) = true ->
      native_string_valid xs = true := by
  intro h
  simp [native_string_valid] at h ⊢
  intro x hx
  exact h.1 x hx

private theorem native_string_valid_append_right
    (xs ys : List native_Char) :
    native_string_valid (xs ++ ys) = true ->
      native_string_valid ys = true := by
  intro h
  simp [native_string_valid] at h ⊢
  intro x hx
  exact h.2 x hx

private theorem nativeListInRe_mk_concat_congr_valid
    (xs : List native_Char) (r r' s s' : SmtRegLan)
    (hxs : native_string_valid xs = true)
    (hr :
      ∀ ys : List native_Char,
        native_string_valid ys = true ->
          nativeListInRe ys r = nativeListInRe ys r')
    (hs :
      ∀ ys : List native_Char,
        native_string_valid ys = true ->
          nativeListInRe ys s = nativeListInRe ys s') :
    nativeListInRe xs (native_re_mk_concat r s) =
      nativeListInRe xs (native_re_mk_concat r' s') := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    rcases
      (nativeListInRe_mk_concat_true_iff_exists_append xs r s).1 h
        with ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
    have hAppendValid : native_string_valid (xs₁ ++ xs₂) = true := by
      rw [hAppend]
      exact hxs
    have hValid₁ := native_string_valid_append_left xs₁ xs₂ hAppendValid
    have hValid₂ := native_string_valid_append_right xs₁ xs₂ hAppendValid
    apply (nativeListInRe_mk_concat_true_iff_exists_append xs r' s').2
    refine ⟨xs₁, xs₂, hAppend, ?_, ?_⟩
    · rwa [← hr xs₁ hValid₁]
    · rwa [← hs xs₂ hValid₂]
  · intro h
    rcases
      (nativeListInRe_mk_concat_true_iff_exists_append xs r' s').1 h
        with ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
    have hAppendValid : native_string_valid (xs₁ ++ xs₂) = true := by
      rw [hAppend]
      exact hxs
    have hValid₁ := native_string_valid_append_left xs₁ xs₂ hAppendValid
    have hValid₂ := native_string_valid_append_right xs₁ xs₂ hAppendValid
    apply (nativeListInRe_mk_concat_true_iff_exists_append xs r s).2
    refine ⟨xs₁, xs₂, hAppend, ?_, ?_⟩
    · rwa [hr xs₁ hValid₁]
    · rwa [hs xs₂ hValid₂]

private theorem nativeListInRe_mk_concat_assoc
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

private theorem native_str_in_re_mk_concat_congr_valid
    (str : native_String) (r r' s s' : SmtRegLan)
    (hValid : native_string_valid str = true)
    (hr :
      ∀ str : native_String, native_string_valid str = true ->
        native_str_in_re str r = native_str_in_re str r')
    (hs :
      ∀ str : native_String, native_string_valid str = true ->
        native_str_in_re str s = native_str_in_re str s') :
    native_str_in_re str (native_re_mk_concat r s) =
      native_str_in_re str (native_re_mk_concat r' s') := by
  have hrList :
      ∀ ys : List native_Char,
        native_string_valid ys = true ->
          nativeListInRe ys r = nativeListInRe ys r' := by
    intro ys hys
    have hValueValid :
        native_re_str_valid (impl_native_string_to_values ys) = true := by
      rw [native_re_str_valid_string]
      exact hys
    simpa [Smtm.native_str_in_re, nativeListInRe, hValueValid] using hr ys hys
  have hsList :
      ∀ ys : List native_Char,
        native_string_valid ys = true ->
          nativeListInRe ys s = nativeListInRe ys s' := by
    intro ys hys
    have hValueValid :
        native_re_str_valid (impl_native_string_to_values ys) = true := by
      rw [native_re_str_valid_string]
      exact hys
    simpa [Smtm.native_str_in_re, nativeListInRe, hValueValid] using hs ys hys
  have hValueValid :
      native_re_str_valid (impl_native_string_to_values str) = true := by
    rw [native_re_str_valid_string]
    exact hValid
  simpa [Smtm.native_str_in_re, nativeListInRe, native_re_concat,
    hValueValid] using
    nativeListInRe_mk_concat_congr_valid str r r' s s' hValid hrList hsList

private theorem native_str_in_re_re_concat_congr_valid
    (str : native_String) (r r' s s' : SmtRegLan)
    (hValid : native_string_valid str = true)
    (hr :
      ∀ str : native_String, native_string_valid str = true ->
        native_str_in_re str r = native_str_in_re str r')
    (hs :
      ∀ str : native_String, native_string_valid str = true ->
        native_str_in_re str s = native_str_in_re str s') :
    native_str_in_re str (native_re_concat r s) =
      native_str_in_re str (native_re_concat r' s') := by
  simpa [native_re_concat, native_re_mk_concat] using
    native_str_in_re_mk_concat_congr_valid str r r' s s' hValid hr hs

private theorem native_str_in_re_mk_concat_assoc
    (str : native_String) (r s t : SmtRegLan) :
    native_str_in_re str
        (native_re_mk_concat (native_re_mk_concat r s) t) =
      native_str_in_re str
        (native_re_mk_concat r (native_re_mk_concat s t)) := by
  by_cases hValid : native_string_valid str = true
  · have hValueValid :
        native_re_str_valid (impl_native_string_to_values str) = true := by
      rw [native_re_str_valid_string]
      exact hValid
    simpa [Smtm.native_str_in_re, nativeListInRe, hValueValid] using
      nativeListInRe_mk_concat_assoc str r s t
  · have hInvalid : native_string_valid str = false := by
      cases h : native_string_valid str <;> simp [h] at hValid ⊢
    have hValueInvalid :
        native_re_str_valid (impl_native_string_to_values str) = false := by
      rw [native_re_str_valid_string]
      exact hInvalid
    simp [Smtm.native_str_in_re, hValueInvalid]

private theorem native_str_in_re_re_concat_assoc
    (str : native_String) (r s t : SmtRegLan) :
    native_str_in_re str (native_re_concat (native_re_concat r s) t) =
      native_str_in_re str (native_re_concat r (native_re_concat s t)) := by
  exact native_str_in_re_mk_concat_assoc str r s t

private theorem native_str_in_re_re_concat_right_epsilon
    (str : native_String) (r : SmtRegLan) :
    native_str_in_re str (native_re_concat r SmtRegLan.epsilon) =
      native_str_in_re str r := by
  rw [native_re_concat_right_epsilon]

private theorem native_str_in_re_re_concat_left_epsilon
    (str : native_String) (r : SmtRegLan) :
    native_str_in_re str (native_re_concat SmtRegLan.epsilon r) =
      native_str_in_re str r := by
  rw [native_re_concat_left_epsilon]

private theorem native_str_in_re_re_union_congr_valid
    (str : native_String) (r r' s s' : SmtRegLan)
    (h₁ :
      ∀ str : native_String, native_string_valid str = true ->
        native_str_in_re str r = native_str_in_re str r')
    (h₂ :
      ∀ str : native_String, native_string_valid str = true ->
        native_str_in_re str s = native_str_in_re str s')
    (hValid : native_string_valid str = true) :
    native_str_in_re str (native_re_union r s) =
      native_str_in_re str (native_re_union r' s') := by
  rw [native_str_in_re_re_union, native_str_in_re_re_union,
    h₁ str hValid, h₂ str hValid]

private theorem native_str_in_re_re_union_assoc
    (str : native_String) (r s t : SmtRegLan) :
    native_str_in_re str (native_re_union (native_re_union r s) t) =
      native_str_in_re str (native_re_union r (native_re_union s t)) := by
  rw [native_str_in_re_re_union, native_str_in_re_re_union,
    native_str_in_re_re_union, native_str_in_re_re_union]
  cases native_str_in_re str r <;> cases native_str_in_re str s <;>
    cases native_str_in_re str t <;> rfl

private theorem native_str_in_re_re_union_right_none
    (str : native_String) (r : SmtRegLan) :
    native_str_in_re str (native_re_union r native_re_none) =
      native_str_in_re str r := by
  rw [native_str_in_re_re_union, native_str_in_re_re_none]
  cases native_str_in_re str r <;> rfl

private theorem nativeReExpRec_shift_ext :
    ∀ n r str,
      native_string_valid str = true ->
      native_str_in_re str (native_re_concat r (nativeReExpRec n r)) =
        native_str_in_re str (native_re_concat (nativeReExpRec n r) r) := by
  intro n
  induction n with
  | zero =>
      intro r str hValid
      rw [nativeReExpRec, native_str_in_re_re_concat_right_epsilon,
        native_str_in_re_re_concat_left_epsilon]
  | succ n ih =>
      intro r str hValid
      calc
        native_str_in_re str (native_re_concat r (nativeReExpRec (Nat.succ n) r))
            =
          native_str_in_re str
            (native_re_concat r (native_re_concat (nativeReExpRec n r) r)) := by
              rfl
        _ =
          native_str_in_re str
            (native_re_concat (native_re_concat r (nativeReExpRec n r)) r) := by
              exact (native_str_in_re_re_concat_assoc str r (nativeReExpRec n r) r).symm
        _ =
          native_str_in_re str
            (native_re_concat (native_re_concat (nativeReExpRec n r) r) r) := by
              exact native_str_in_re_re_concat_congr_valid str
                (native_re_concat r (nativeReExpRec n r))
                (native_re_concat (nativeReExpRec n r) r)
                r r
                hValid
                (fun s hs => ih r s hs)
                (fun _ _ => rfl)
        _ =
          native_str_in_re str
            (native_re_concat (nativeReExpRec (Nat.succ n) r) r) := by
              rfl

private theorem nativeRePow_exp_ext :
    ∀ n r str,
      native_string_valid str = true ->
      native_str_in_re str (nativeRePow n r) =
        native_str_in_re str (nativeReExpRec n r) := by
  intro n
  induction n with
  | zero =>
      intro r str hValid
      rfl
  | succ n ih =>
      intro r str hValid
      calc
        native_str_in_re str (nativeRePow (Nat.succ n) r)
            =
          native_str_in_re str (native_re_concat r (nativeReExpRec n r)) := by
            exact native_str_in_re_re_concat_congr_valid str
              r r (nativeRePow n r) (nativeReExpRec n r)
              hValid (fun _ _ => rfl) (fun s hs => ih r s hs)
        _ =
          native_str_in_re str (nativeReExpRec (Nat.succ n) r) := by
            exact nativeReExpRec_shift_ext n r str hValid

def nativeRangeRight : native_Nat -> native_Nat -> SmtRegLan -> SmtRegLan
  | start, 0, r => nativeReExpRec start r
  | start, Nat.succ n, r =>
      native_re_union (nativeReExpRec start r)
        (nativeRangeRight (Nat.succ start) n r)

private def nativeLoopElim : native_Nat -> SmtRegLan -> SmtRegLan -> SmtRegLan
  | 0, _r, acc => acc
  | Nat.succ n, r, acc =>
      native_re_union acc (nativeLoopElim n r (native_re_concat r acc))

private def nativeLoopRaw : native_Nat -> SmtRegLan -> SmtRegLan -> SmtRegLan
  | 0, _r, acc => native_re_union acc native_re_none
  | Nat.succ n, r, acc =>
      native_re_union acc (nativeLoopRaw n r (native_re_concat r acc))

private def nativeLoopOuter : native_Nat -> SmtRegLan -> SmtRegLan -> SmtRegLan
  | 0, _r, acc => acc
  | Nat.succ n, r, acc => nativeLoopRaw (Nat.succ n) r acc

private theorem nativeLoopRaw_elim_ext :
    ∀ len r acc str,
      native_string_valid str = true ->
      native_str_in_re str (nativeLoopRaw len r acc) =
        native_str_in_re str (nativeLoopElim len r acc) := by
  intro len
  induction len with
  | zero =>
      intro r acc str hValid
      simp [nativeLoopRaw, nativeLoopElim, native_str_in_re_re_union_right_none]
  | succ len ih =>
      intro r acc str hValid
      rw [nativeLoopRaw, nativeLoopElim]
      exact native_str_in_re_re_union_congr_valid str
        acc acc
        (nativeLoopRaw len r (native_re_concat r acc))
        (nativeLoopElim len r (native_re_concat r acc))
        (fun _ _ => rfl)
        (fun s hs => ih r (native_re_concat r acc) s hs)
        hValid

private theorem nativeLoopOuter_elim_ext
    (len : native_Nat) (r acc : SmtRegLan) (str : native_String)
    (hValid : native_string_valid str = true) :
    native_str_in_re str (nativeLoopOuter len r acc) =
      native_str_in_re str (nativeLoopElim len r acc) := by
  cases len with
  | zero => rfl
  | succ n =>
      exact nativeLoopRaw_elim_ext (Nat.succ n) r acc str hValid

private theorem nativeLoopElim_range_ext :
    ∀ len start r str,
      native_string_valid str = true ->
      native_str_in_re str
          (nativeLoopElim len r (nativeRePow start r)) =
        native_str_in_re str (nativeRangeRight start len r) := by
  intro len
  induction len with
  | zero =>
      intro start r str hValid
      exact nativeRePow_exp_ext start r str hValid
  | succ len ih =>
      intro start r str hValid
      rw [nativeLoopElim, nativeRangeRight]
      exact native_str_in_re_re_union_congr_valid str
        (nativeRePow start r) (nativeReExpRec start r)
        (nativeLoopElim len r (native_re_concat r (nativeRePow start r)))
        (nativeRangeRight (Nat.succ start) len r)
        (fun s hs => nativeRePow_exp_ext start r s hs)
        (fun s hs => by
          change native_str_in_re s
              (nativeLoopElim len r (nativeRePow (Nat.succ start) r)) =
            native_str_in_re s (nativeRangeRight (Nat.succ start) len r)
          exact ih (Nat.succ start) r s hs)
        hValid

private theorem nativeRangeRight_append_last_ext :
    ∀ len start r str,
      native_string_valid str = true ->
      native_str_in_re str
          (native_re_union (nativeRangeRight start len r)
            (nativeReExpRec (start + Nat.succ len) r)) =
        native_str_in_re str (nativeRangeRight start (Nat.succ len) r) := by
  intro len
  induction len with
  | zero =>
      intro start r str hValid
      rfl
  | succ len ih =>
      intro start r str hValid
      rw [nativeRangeRight, nativeRangeRight]
      calc
        native_str_in_re str
            (native_re_union
              (native_re_union (nativeReExpRec start r)
                (nativeRangeRight (Nat.succ start) len r))
              (nativeReExpRec (start + Nat.succ (Nat.succ len)) r))
            =
          native_str_in_re str
            (native_re_union (nativeReExpRec start r)
              (native_re_union (nativeRangeRight (Nat.succ start) len r)
                (nativeReExpRec (Nat.succ start + Nat.succ len) r))) := by
              have hIdx :
                  start + Nat.succ (Nat.succ len) =
                    Nat.succ start + Nat.succ len := by
                simp [Nat.succ_eq_add_one, Nat.add_comm,
                  Nat.add_left_comm]
              rw [hIdx]
              exact native_str_in_re_re_union_assoc str
                (nativeReExpRec start r)
                (nativeRangeRight (Nat.succ start) len r)
                (nativeReExpRec (Nat.succ start + Nat.succ len) r)
        _ =
          native_str_in_re str
            (native_re_union (nativeReExpRec start r)
              (nativeRangeRight (Nat.succ start) (Nat.succ len) r)) := by
              exact native_str_in_re_re_union_congr_valid str
                (nativeReExpRec start r) (nativeReExpRec start r)
                (native_re_union (nativeRangeRight (Nat.succ start) len r)
                  (nativeReExpRec (Nat.succ start + Nat.succ len) r))
                (nativeRangeRight (Nat.succ start) (Nat.succ len) r)
                (fun _ _ => rfl)
                (fun s hs => ih (Nat.succ start) r s hs)
                hValid

def nativeReLoopRec :
    native_Nat -> native_Int -> native_Int -> SmtRegLan -> SmtRegLan
  | 0, lo, _hi, r => nativeReExpRec (native_int_to_nat lo) r
  | Nat.succ n, lo, hi, r =>
      native_re_union
        (nativeReLoopRec n lo (native_zplus hi (native_zneg 1)) r)
        (nativeReExpRec (native_int_to_nat hi) r)

theorem model_eval_re_loop_rec_reglan_eq :
    ∀ n lo hi r,
      __smtx_re_loop_rec n (SmtValue.Numeral lo)
          (SmtValue.Numeral hi) (SmtValue.RegLan r) =
        SmtValue.RegLan (nativeReLoopRec n lo hi r) := by
  intro n
  induction n with
  | zero =>
      intro lo hi r
      simp [__smtx_re_loop_rec, nativeReLoopRec,
        model_eval_re_exp_rec_reglan_eq, __smtx_model_eval_re_exp]
  | succ n ih =>
      intro lo hi r
      simp [__smtx_re_loop_rec, nativeReLoopRec, ih,
        model_eval_re_exp_rec_reglan_eq, __smtx_model_eval_re_exp,
        __smtx_model_eval_re_union]

private theorem native_int_to_nat_add_nat
    (lo : native_Int) (n : native_Nat)
    (hlo : 0 ≤ lo) :
    native_int_to_nat (lo + Int.ofNat n) =
      native_int_to_nat lo + n := by
  simp [native_int_to_nat]
  have h : 0 ≤ lo + Int.ofNat n :=
    Int.add_nonneg hlo (Int.natCast_nonneg n)
  apply Int.ofNat.inj
  change (↑(Int.toNat (lo + Int.ofNat n)) : Int) =
    ↑(Int.toNat lo + n)
  rw [Int.toNat_of_nonneg h]
  calc
    lo + Int.ofNat n = (↑(Int.toNat lo) : Int) + Int.ofNat n := by
      rw [Int.toNat_of_nonneg hlo]
    _ = ↑(Int.toNat lo + n) := by simp

theorem nativeReLoopRec_range_ext :
    ∀ len lo r str,
      0 ≤ lo ->
      native_string_valid str = true ->
      native_str_in_re str
          (nativeReLoopRec len lo (lo + Int.ofNat len) r) =
        native_str_in_re str (nativeRangeRight (native_int_to_nat lo) len r) := by
  intro len
  induction len with
  | zero =>
      intro lo r str hlo hValid
      rfl
  | succ len ih =>
      intro lo r str hlo hValid
      rw [nativeReLoopRec]
      have hPred :
          native_zplus (lo + Int.ofNat (Nat.succ len)) (native_zneg 1) =
            lo + Int.ofNat len := by
        simp [native_zplus, native_zneg]
        change (lo + (Int.ofNat len + 1)) + -1 = lo + Int.ofNat len
        rw [← Int.add_assoc lo (Int.ofNat len) 1]
        rw [Int.add_assoc (lo + Int.ofNat len) 1 (-1)]
        simp
      have hHiNat :
          native_int_to_nat (lo + Int.ofNat (Nat.succ len)) =
            native_int_to_nat lo + Nat.succ len :=
        native_int_to_nat_add_nat lo (Nat.succ len) hlo
      rw [hPred, hHiNat]
      calc
        native_str_in_re str
            (native_re_union (nativeReLoopRec len lo (lo + Int.ofNat len) r)
              (nativeReExpRec (native_int_to_nat lo + Nat.succ len) r))
            =
          native_str_in_re str
            (native_re_union (nativeRangeRight (native_int_to_nat lo) len r)
              (nativeReExpRec (native_int_to_nat lo + Nat.succ len) r)) := by
              exact native_str_in_re_re_union_congr_valid str
                (nativeReLoopRec len lo (lo + Int.ofNat len) r)
                (nativeRangeRight (native_int_to_nat lo) len r)
                (nativeReExpRec (native_int_to_nat lo + Nat.succ len) r)
                (nativeReExpRec (native_int_to_nat lo + Nat.succ len) r)
                (fun s hs => ih lo r s hlo hs)
                (fun _ _ => rfl)
                hValid
        _ =
          native_str_in_re str
            (nativeRangeRight (native_int_to_nat lo) (Nat.succ len) r) := by
              exact nativeRangeRight_append_last_ext len
                (native_int_to_nat lo) r str hValid

private theorem eo_typeof_ne_stuck_of_smt_reglan
    (a : Term)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan) :
    __eo_typeof a ≠ Term.Stuck := by
  have hNN : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [haTy]
    intro h
    cases h
  have hMatch := TranslationProofs.eo_to_smt_typeof_matches_translation a hNN
  intro hStuck
  rw [hStuck] at hMatch
  rw [haTy] at hMatch
  cases hMatch

private theorem term_ne_stuck_of_smt_reglan
    (a : Term)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan) :
    a ≠ Term.Stuck := by
  intro h
  subst a
  exact (eo_typeof_ne_stuck_of_smt_reglan Term.Stuck haTy) rfl

private theorem term_ne_stuck_of_eval_reglan
    (M : SmtModel) (t : Term) (rv : SmtRegLan) :
    __smtx_model_eval M (__eo_to_smt t) = SmtValue.RegLan rv ->
    t ≠ Term.Stuck := by
  intro hEval h
  subst t
  change __smtx_model_eval M SmtTerm.None = SmtValue.RegLan rv at hEval
  simp [__smtx_model_eval] at hEval

private theorem eo_mk_apply_of_ne_stuck
    {f x : Term}
    (hf : f ≠ Term.Stuck) (hx : x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

private theorem re_concat_apply_head_ne_stuck (a : Term) :
    Term.Apply (Term.UOp UserOp.re_concat) a ≠ Term.Stuck := by
  intro h
  cases h

private theorem re_union_apply_head_ne_stuck (a : Term) :
    Term.Apply (Term.UOp UserOp.re_union) a ≠ Term.Stuck := by
  intro h
  cases h

private theorem eo_is_list_true_of_get_nil_eq
    {f x nil : Term}
    (hf : f ≠ Term.Stuck) (hx : x ≠ Term.Stuck)
    (hNil : __eo_get_nil_rec f x = nil)
    (hNilNe : nil ≠ Term.Stuck) :
    __eo_is_list f x = Term.Boolean true := by
  have hGetNe : __eo_get_nil_rec f x ≠ Term.Stuck := by
    intro hGet
    rw [hGet] at hNil
    exact hNilNe hNil.symm
  cases f <;> cases x <;>
    simp [__eo_is_list, __eo_is_ok, native_teq, native_not,
      SmtEval.native_not, hGetNe] at hf hx hNil hNilNe ⊢

private theorem re_list_repeat_rec_zero_eq
    (a : Term) (hANe : a ≠ Term.Stuck) :
    __eo_list_repeat_rec (Term.UOp UserOp.re_concat) a (0 : native_Nat) =
      __eo_nil (Term.UOp UserOp.re_concat) (__eo_typeof a) := by
  cases a <;> simp [__eo_list_repeat_rec] at hANe ⊢

private theorem re_list_repeat_rec_succ_eq
    (a : Term) (hANe : a ≠ Term.Stuck) (n : native_Nat) :
    __eo_list_repeat_rec (Term.UOp UserOp.re_concat) a (Nat.succ n) =
      __eo_mk_apply
        (Term.Apply (Term.UOp UserOp.re_concat) a)
        (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a n) := by
  cases a <;> simp [__eo_list_repeat_rec] at hANe ⊢

private theorem re_list_repeat_rec_ne_stuck
    (a : Term)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan) :
    ∀ n : native_Nat,
      __eo_list_repeat_rec (Term.UOp UserOp.re_concat) a n ≠ Term.Stuck := by
  intro n
  have hANe := term_ne_stuck_of_smt_reglan a haTy
  induction n with
  | zero =>
      have hTyNe := eo_typeof_ne_stuck_of_smt_reglan a haTy
      rw [re_list_repeat_rec_zero_eq a hANe]
      cases hTy : __eo_typeof a
      case Stuck => exact False.elim (hTyNe hTy)
      all_goals simp [__eo_nil]
  | succ n ih =>
      rw [re_list_repeat_rec_succ_eq a hANe n]
      rw [eo_mk_apply_of_ne_stuck (re_concat_apply_head_ne_stuck a) ih]
      intro h
      cases h

private theorem re_list_repeat_rec_get_nil
    (a : Term)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan) :
    ∀ n : native_Nat,
      __eo_get_nil_rec (Term.UOp UserOp.re_concat)
        (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a n) =
        Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []) := by
  intro n
  have hANe := term_ne_stuck_of_smt_reglan a haTy
  induction n with
  | zero =>
      have hTyNe := eo_typeof_ne_stuck_of_smt_reglan a haTy
      rw [re_list_repeat_rec_zero_eq a hANe]
      cases hTy : __eo_typeof a
      case Stuck => exact False.elim (hTyNe hTy)
      all_goals
        simp [__eo_nil, __eo_get_nil_rec, __eo_is_list_nil, __eo_requires,
          native_ite, native_teq, native_not, SmtEval.native_not]
  | succ n ih =>
      have hTailNe := re_list_repeat_rec_ne_stuck a haTy n
      rw [re_list_repeat_rec_succ_eq a hANe n]
      rw [eo_mk_apply_of_ne_stuck (re_concat_apply_head_ne_stuck a) hTailNe]
      simp [__eo_get_nil_rec, __eo_requires, native_ite, native_teq,
        native_not, SmtEval.native_not, ih]

private theorem re_list_repeat_rec_is_list
    (a : Term)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (n : native_Nat) :
    __eo_is_list (Term.UOp UserOp.re_concat)
      (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a n) =
      Term.Boolean true := by
  have hNil := re_list_repeat_rec_get_nil a haTy n
  have hXNe := re_list_repeat_rec_ne_stuck a haTy n
  exact eo_is_list_true_of_get_nil_eq
    (by intro h; cases h) hXNe hNil (by intro h; cases h)

private theorem re_list_repeat_rec_succ_not_nil
    (a : Term)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (n : native_Nat) :
    __eo_is_list_nil (Term.UOp UserOp.re_concat)
      (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a (Nat.succ n)) =
      Term.Boolean false := by
  have hANe := term_ne_stuck_of_smt_reglan a haTy
  have hTailNe := re_list_repeat_rec_ne_stuck a haTy n
  rw [re_list_repeat_rec_succ_eq a hANe n]
  rw [eo_mk_apply_of_ne_stuck (re_concat_apply_head_ne_stuck a) hTailNe]
  simp [__eo_is_list_nil]

private theorem re_list_repeat_rec_eval_eq_pow
    (M : SmtModel) (a : Term) (rv : SmtRegLan)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (haEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan rv) :
    ∀ n : native_Nat,
      __smtx_model_eval M
          (__eo_to_smt (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a n)) =
        SmtValue.RegLan (nativeRePow n rv) := by
  intro n
  have hANe := term_ne_stuck_of_smt_reglan a haTy
  induction n with
  | zero =>
      have hTyNe := eo_typeof_ne_stuck_of_smt_reglan a haTy
      rw [re_list_repeat_rec_zero_eq a hANe]
      cases hTy : __eo_typeof a
      case Stuck => exact False.elim (hTyNe hTy)
      all_goals
        simp [__eo_nil, nativeRePow]
        change __smtx_model_eval M
            (SmtTerm.str_to_re (SmtTerm.String [])) =
          SmtValue.RegLan SmtRegLan.epsilon
        simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
          native_str_to_re, impl_native_re_of_list, native_pack_string,
          native_pack_seq, native_unpack_seq]
  | succ n ih =>
      have hTailNe := re_list_repeat_rec_ne_stuck a haTy n
      rw [re_list_repeat_rec_succ_eq a hANe n]
      rw [eo_mk_apply_of_ne_stuck (re_concat_apply_head_ne_stuck a) hTailNe]
      change __smtx_model_eval M
          (SmtTerm.re_concat (__eo_to_smt a)
            (__eo_to_smt
              (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a n))) =
        SmtValue.RegLan (nativeRePow (Nat.succ n) rv)
      rw [__smtx_model_eval.eq_114, haEval, ih]
      simp [__smtx_model_eval_re_concat, nativeRePow]

private theorem re_list_repeat_singleton_eval_eq_pow
    (M : SmtModel) (a : Term) (rv : SmtRegLan)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (haEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan rv) :
    ∀ n : native_Nat,
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
              (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a n))) =
        SmtValue.RegLan (nativeRePow n rv) := by
  intro n
  have hANe := term_ne_stuck_of_smt_reglan a haTy
  cases n with
  | zero =>
      have hTyNe := eo_typeof_ne_stuck_of_smt_reglan a haTy
      rw [re_list_repeat_rec_zero_eq a hANe]
      cases hTy : __eo_typeof a
      case Stuck => exact False.elim (hTyNe hTy)
      all_goals
        simp [__eo_nil, __eo_list_singleton_elim,
          __eo_list_singleton_elim_2, __eo_is_list, __eo_get_nil_rec,
          __eo_is_list_nil, __eo_is_ok, __eo_requires, native_ite,
          native_teq, native_not, SmtEval.native_not, nativeRePow]
        change __smtx_model_eval M
            (SmtTerm.str_to_re (SmtTerm.String [])) =
          SmtValue.RegLan SmtRegLan.epsilon
        simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
          native_str_to_re, impl_native_re_of_list, native_pack_string,
          native_pack_seq, native_unpack_seq]
  | succ n =>
      cases n with
      | zero =>
          have hTailNe :=
            re_list_repeat_rec_ne_stuck a haTy (0 : native_Nat)
          rw [re_list_repeat_rec_succ_eq a hANe (0 : native_Nat)]
          rw [eo_mk_apply_of_ne_stuck (re_concat_apply_head_ne_stuck a) hTailNe]
          rw [re_list_repeat_rec_zero_eq a hANe]
          have hTyNe := eo_typeof_ne_stuck_of_smt_reglan a haTy
          cases hTy : __eo_typeof a
          case Stuck => exact False.elim (hTyNe hTy)
          all_goals
            simp [__eo_nil, __eo_list_singleton_elim,
              __eo_list_singleton_elim_2, __eo_is_list, __eo_get_nil_rec,
              __eo_is_list_nil, __eo_is_ok, __eo_requires, native_ite,
              native_teq, native_not, SmtEval.native_not, nativeRePow]
            rw [native_re_concat_right_epsilon]
            exact haEval
      | succ n =>
          have hTailNe :=
            re_list_repeat_rec_ne_stuck a haTy (Nat.succ n)
          have hTailEval :=
            re_list_repeat_rec_eval_eq_pow M a rv haTy haEval (Nat.succ n)
          have hIsList :=
            re_list_repeat_rec_is_list a haTy (Nat.succ (Nat.succ n))
          have hTailNotNil :=
            re_list_repeat_rec_succ_not_nil a haTy n
          change
            __smtx_model_eval M
              (__eo_to_smt
                (__eo_requires
                  (__eo_is_list (Term.UOp UserOp.re_concat)
                    (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a
                      (Nat.succ (Nat.succ n))))
                  (Term.Boolean true)
                  (__eo_list_singleton_elim_2
                    (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a
                      (Nat.succ (Nat.succ n)))))) =
            SmtValue.RegLan (nativeRePow (Nat.succ (Nat.succ n)) rv)
          rw [hIsList]
          simp [__eo_requires, native_ite, native_teq, native_not,
            SmtEval.native_not]
          rw [re_list_repeat_rec_succ_eq a hANe (Nat.succ n)]
          rw [eo_mk_apply_of_ne_stuck (re_concat_apply_head_ne_stuck a) hTailNe]
          simp [__eo_list_singleton_elim_2, hTailNotNil, __eo_ite,
            native_ite, native_teq]
          change __smtx_model_eval M
              (SmtTerm.re_concat (__eo_to_smt a)
                (__eo_to_smt
                  (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a
                    (Nat.succ n)))) =
            SmtValue.RegLan (nativeRePow (Nat.succ (Nat.succ n)) rv)
          rw [__smtx_model_eval.eq_114, haEval, hTailEval]
          simp [__smtx_model_eval_re_concat, nativeRePow]

private def zeroList : native_Nat -> Term
  | 0 => Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) (Term.UOp UserOp.Int)
  | Nat.succ n =>
      Term.Apply
        (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) (Term.Numeral 0))
        (zeroList n)

private theorem typed_zero_list_repeat_rec_eq :
    ∀ n : native_Nat,
      __eo_list_repeat_rec (Term.UOp UserOp._at__at_TypedList_cons)
        (Term.Numeral 0) n = zeroList n := by
  have zeroList_ne_stuck : ∀ n : native_Nat, zeroList n ≠ Term.Stuck := by
    intro n
    cases n <;> intro h <;> cases h
  intro n
  induction n with
  | zero =>
      change __eo_nil (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.UOp UserOp.Int) =
        Term.Apply (Term.UOp UserOp._at__at_TypedList_nil)
          (Term.UOp UserOp.Int)
      simp [__eo_nil, __eo_nil__at__at_TypedList_cons]
  | succ n ih =>
      change __eo_mk_apply
          (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
            (Term.Numeral 0))
          (__eo_list_repeat_rec (Term.UOp UserOp._at__at_TypedList_cons)
            (Term.Numeral 0) n) =
        zeroList (Nat.succ n)
      rw [ih]
      have hHead :
          Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
              (Term.Numeral 0) ≠ Term.Stuck := by
        simp
      rw [eo_mk_apply_of_ne_stuck hHead (zeroList_ne_stuck n)]
      rfl

private theorem re_loop_elim_raw_rec_eval_eq
    (M : SmtModel) (a : Term) (rv : SmtRegLan)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (haEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan rv) :
    ∀ len start : native_Nat,
      __smtx_model_eval M
        (__eo_to_smt
          (__str_mk_re_loop_elim_rec (zeroList len) a
            (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start))) =
        SmtValue.RegLan (nativeLoopRaw len rv (nativeRePow start rv)) := by
  intro len
  induction len with
  | zero =>
      intro start
      have hANe := term_ne_stuck_of_smt_reglan a haTy
      have hRepNe := re_list_repeat_rec_ne_stuck a haTy start
      have hSingEval :=
        re_list_repeat_singleton_eval_eq_pow M a rv haTy haEval start
      have hSingNe :
          __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
              (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start) ≠
            Term.Stuck :=
        term_ne_stuck_of_eval_reglan M _ _ hSingEval
      simp [zeroList, __str_mk_re_loop_elim_rec]
      rw [eo_mk_apply_of_ne_stuck (by intro h; cases h) hSingNe]
      rw [eo_mk_apply_of_ne_stuck (re_union_apply_head_ne_stuck _) (by intro h; cases h)]
      change __smtx_model_eval M
          (SmtTerm.re_union
            (__eo_to_smt
              (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
                (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start)))
            SmtTerm.re_none) =
        SmtValue.RegLan (nativeLoopRaw 0 rv (nativeRePow start rv))
      rw [__smtx_model_eval.eq_116, hSingEval]
      have hNoneEval :
          __smtx_model_eval M SmtTerm.re_none =
            SmtValue.RegLan native_re_none := by
        simp [__smtx_model_eval]
      rw [hNoneEval]
      rfl
  | succ len ih =>
      intro start
      have hSingEval :=
        re_list_repeat_singleton_eval_eq_pow M a rv haTy haEval start
      have hSingNe :
          __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
              (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start) ≠
            Term.Stuck :=
        term_ne_stuck_of_eval_reglan M _ _ hSingEval
      have hANe := term_ne_stuck_of_smt_reglan a haTy
      have hRepNe := re_list_repeat_rec_ne_stuck a haTy start
      have hStartSucc :
          __eo_list_repeat_rec (Term.UOp UserOp.re_concat) a (Nat.succ start) =
            Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a)
              (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start) := by
        rw [re_list_repeat_rec_succ_eq a hANe start]
        exact eo_mk_apply_of_ne_stuck (re_concat_apply_head_ne_stuck a) hRepNe
      have hTailEval :
          __smtx_model_eval M
            (__eo_to_smt
              (__str_mk_re_loop_elim_rec (zeroList len) a
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a)
                  (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start)))) =
            SmtValue.RegLan
              (nativeLoopRaw len rv (native_re_concat rv (nativeRePow start rv))) := by
        rw [← hStartSucc]
        exact ih (Nat.succ start)
      have hTailNe :
          __str_mk_re_loop_elim_rec (zeroList len) a
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a)
              (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start)) ≠
            Term.Stuck :=
        term_ne_stuck_of_eval_reglan M _ _ hTailEval
      simp [zeroList, __str_mk_re_loop_elim_rec]
      rw [eo_mk_apply_of_ne_stuck (by intro h; cases h) hSingNe]
      rw [eo_mk_apply_of_ne_stuck (re_union_apply_head_ne_stuck _) hTailNe]
      change __smtx_model_eval M
          (SmtTerm.re_union
            (__eo_to_smt
              (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
                (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start)))
            (__eo_to_smt
              (__str_mk_re_loop_elim_rec (zeroList len) a
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a)
                  (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start))))) =
        SmtValue.RegLan
          (nativeLoopRaw (Nat.succ len) rv (nativeRePow start rv))
      rw [__smtx_model_eval.eq_116, hSingEval, hTailEval]
      simp [__smtx_model_eval_re_union, nativeLoopRaw]

private theorem re_loop_elim_raw_rec_not_nil
    (M : SmtModel) (a : Term) (rv : SmtRegLan)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (haEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan rv) :
    ∀ len start : native_Nat,
      __eo_is_list_nil (Term.UOp UserOp.re_union)
        (__str_mk_re_loop_elim_rec (zeroList len) a
          (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start)) =
        Term.Boolean false := by
  intro len
  induction len with
  | zero =>
      intro start
      have hANe := term_ne_stuck_of_smt_reglan a haTy
      have hRepNe := re_list_repeat_rec_ne_stuck a haTy start
      have hSingEval :=
        re_list_repeat_singleton_eval_eq_pow M a rv haTy haEval start
      have hSingNe :
          __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
              (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start) ≠
            Term.Stuck :=
        term_ne_stuck_of_eval_reglan M _ _ hSingEval
      simp [zeroList, __str_mk_re_loop_elim_rec]
      rw [eo_mk_apply_of_ne_stuck (by intro h; cases h) hSingNe]
      rw [eo_mk_apply_of_ne_stuck (re_union_apply_head_ne_stuck _) (by intro h; cases h)]
      simp [__eo_is_list_nil]
  | succ len ih =>
      intro start
      have hANe := term_ne_stuck_of_smt_reglan a haTy
      have hRepNe := re_list_repeat_rec_ne_stuck a haTy start
      have hSingEval :=
        re_list_repeat_singleton_eval_eq_pow M a rv haTy haEval start
      have hSingNe :
          __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
              (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start) ≠
            Term.Stuck :=
        term_ne_stuck_of_eval_reglan M _ _ hSingEval
      have hStartSucc :
          __eo_list_repeat_rec (Term.UOp UserOp.re_concat) a (Nat.succ start) =
            Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a)
              (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start) := by
        rw [re_list_repeat_rec_succ_eq a hANe start]
        exact eo_mk_apply_of_ne_stuck (re_concat_apply_head_ne_stuck a) hRepNe
      have hTailEval :
          __smtx_model_eval M
            (__eo_to_smt
              (__str_mk_re_loop_elim_rec (zeroList len) a
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a)
                  (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start)))) =
            SmtValue.RegLan
              (nativeLoopRaw len rv (native_re_concat rv (nativeRePow start rv))) := by
        rw [← hStartSucc]
        exact re_loop_elim_raw_rec_eval_eq M a rv haTy haEval len (Nat.succ start)
      have hTailNe :
          __str_mk_re_loop_elim_rec (zeroList len) a
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a)
              (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start)) ≠
            Term.Stuck :=
        term_ne_stuck_of_eval_reglan M _ _ hTailEval
      simp [zeroList, __str_mk_re_loop_elim_rec]
      rw [eo_mk_apply_of_ne_stuck (by intro h; cases h) hSingNe]
      rw [eo_mk_apply_of_ne_stuck (re_union_apply_head_ne_stuck _) hTailNe]
      simp [__eo_is_list_nil]

private theorem re_loop_elim_raw_rec_get_nil
    (M : SmtModel) (a : Term) (rv : SmtRegLan)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (haEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan rv) :
    ∀ len start : native_Nat,
      __eo_get_nil_rec (Term.UOp UserOp.re_union)
        (__str_mk_re_loop_elim_rec (zeroList len) a
          (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start)) =
        Term.UOp UserOp.re_none := by
  intro len
  induction len with
  | zero =>
      intro start
      have hANe := term_ne_stuck_of_smt_reglan a haTy
      have hRepNe := re_list_repeat_rec_ne_stuck a haTy start
      have hSingEval :=
        re_list_repeat_singleton_eval_eq_pow M a rv haTy haEval start
      have hSingNe :
          __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
              (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start) ≠
            Term.Stuck :=
        term_ne_stuck_of_eval_reglan M _ _ hSingEval
      simp [zeroList, __str_mk_re_loop_elim_rec]
      rw [eo_mk_apply_of_ne_stuck (by intro h; cases h) hSingNe]
      rw [eo_mk_apply_of_ne_stuck (re_union_apply_head_ne_stuck _) (by intro h; cases h)]
      simp [__eo_get_nil_rec, __eo_is_list_nil, __eo_requires,
        native_ite, native_teq, native_not, SmtEval.native_not]
  | succ len ih =>
      intro start
      have hANe := term_ne_stuck_of_smt_reglan a haTy
      have hRepNe := re_list_repeat_rec_ne_stuck a haTy start
      have hSingEval :=
        re_list_repeat_singleton_eval_eq_pow M a rv haTy haEval start
      have hSingNe :
          __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
              (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start) ≠
            Term.Stuck :=
        term_ne_stuck_of_eval_reglan M _ _ hSingEval
      have hStartSucc :
          __eo_list_repeat_rec (Term.UOp UserOp.re_concat) a (Nat.succ start) =
            Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a)
              (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start) := by
        rw [re_list_repeat_rec_succ_eq a hANe start]
        exact eo_mk_apply_of_ne_stuck (re_concat_apply_head_ne_stuck a) hRepNe
      have hTailEval :
          __smtx_model_eval M
            (__eo_to_smt
              (__str_mk_re_loop_elim_rec (zeroList len) a
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a)
                  (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start)))) =
            SmtValue.RegLan
              (nativeLoopRaw len rv (native_re_concat rv (nativeRePow start rv))) := by
        rw [← hStartSucc]
        exact re_loop_elim_raw_rec_eval_eq M a rv haTy haEval len (Nat.succ start)
      have hTailNe :
          __str_mk_re_loop_elim_rec (zeroList len) a
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a)
              (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start)) ≠
            Term.Stuck :=
        term_ne_stuck_of_eval_reglan M _ _ hTailEval
      have hTailNil :
          __eo_get_nil_rec (Term.UOp UserOp.re_union)
            (__str_mk_re_loop_elim_rec (zeroList len) a
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a)
                (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start))) =
            Term.UOp UserOp.re_none := by
        rw [← hStartSucc]
        exact ih (Nat.succ start)
      simp [zeroList, __str_mk_re_loop_elim_rec]
      rw [eo_mk_apply_of_ne_stuck (by intro h; cases h) hSingNe]
      rw [eo_mk_apply_of_ne_stuck (re_union_apply_head_ne_stuck _) hTailNe]
      simp [__eo_get_nil_rec, __eo_requires, native_ite, native_teq,
        native_not, SmtEval.native_not, hTailNil]

private theorem re_loop_elim_outer_eval_eq
    (M : SmtModel) (a : Term) (rv : SmtRegLan)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (haEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan rv) :
    ∀ len start : native_Nat,
      __smtx_model_eval M
        (__eo_to_smt
          (__eo_list_singleton_elim (Term.UOp UserOp.re_union)
            (__str_mk_re_loop_elim_rec (zeroList len) a
              (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start)))) =
        SmtValue.RegLan (nativeLoopOuter len rv (nativeRePow start rv)) := by
  intro len
  cases len with
  | zero =>
      intro start
      have hANe := term_ne_stuck_of_smt_reglan a haTy
      have hRepNe := re_list_repeat_rec_ne_stuck a haTy start
      have hSingEval :=
        re_list_repeat_singleton_eval_eq_pow M a rv haTy haEval start
      have hSingNe :
          __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
              (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start) ≠
            Term.Stuck :=
        term_ne_stuck_of_eval_reglan M _ _ hSingEval
      change __smtx_model_eval M
          (__eo_to_smt
            (__eo_requires
              (__eo_is_list (Term.UOp UserOp.re_union)
                (__str_mk_re_loop_elim_rec (zeroList 0) a
                  (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start)))
              (Term.Boolean true)
              (__eo_list_singleton_elim_2
                (__str_mk_re_loop_elim_rec (zeroList 0) a
                  (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start))))) =
        SmtValue.RegLan (nativeLoopOuter 0 rv (nativeRePow start rv))
      simp [zeroList, __str_mk_re_loop_elim_rec]
      rw [eo_mk_apply_of_ne_stuck (by intro h; cases h) hSingNe]
      rw [eo_mk_apply_of_ne_stuck (re_union_apply_head_ne_stuck _) (by intro h; cases h)]
      simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil, __eo_is_ok,
        __eo_requires, __eo_list_singleton_elim_2, __eo_ite, native_ite,
        native_teq, native_not, SmtEval.native_not, nativeLoopOuter]
      exact hSingEval
  | succ len =>
      intro start
      have hRawEval :=
        re_loop_elim_raw_rec_eval_eq M a rv haTy haEval (Nat.succ len) start
      have hRawNe :=
        term_ne_stuck_of_eval_reglan M _ _ hRawEval
      have hNotNil :=
        re_loop_elim_raw_rec_not_nil M a rv haTy haEval (Nat.succ len) start
      have hList : __eo_is_list (Term.UOp UserOp.re_union)
          (__str_mk_re_loop_elim_rec (zeroList (Nat.succ len)) a
            (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start)) =
          Term.Boolean true := by
        exact eo_is_list_true_of_get_nil_eq
          (by intro h; cases h) hRawNe
          (re_loop_elim_raw_rec_get_nil M a rv haTy haEval (Nat.succ len) start)
          (by intro h; cases h)
      change __smtx_model_eval M
          (__eo_to_smt
            (__eo_requires
              (__eo_is_list (Term.UOp UserOp.re_union)
                (__str_mk_re_loop_elim_rec (zeroList (Nat.succ len)) a
                  (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start)))
              (Term.Boolean true)
              (__eo_list_singleton_elim_2
                (__str_mk_re_loop_elim_rec (zeroList (Nat.succ len)) a
                  (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start))))) =
        SmtValue.RegLan
          (nativeLoopOuter (Nat.succ len) rv (nativeRePow start rv))
      rw [hList]
      simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
      have hANe := term_ne_stuck_of_smt_reglan a haTy
      have hRepNe := re_list_repeat_rec_ne_stuck a haTy start
      have hSingEval :=
        re_list_repeat_singleton_eval_eq_pow M a rv haTy haEval start
      have hSingNe :
          __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
              (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start) ≠
            Term.Stuck :=
        term_ne_stuck_of_eval_reglan M _ _ hSingEval
      have hStartSucc :
          __eo_list_repeat_rec (Term.UOp UserOp.re_concat) a (Nat.succ start) =
            Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a)
              (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start) := by
        rw [re_list_repeat_rec_succ_eq a hANe start]
        exact eo_mk_apply_of_ne_stuck (re_concat_apply_head_ne_stuck a) hRepNe
      have hTailEval :
          __smtx_model_eval M
            (__eo_to_smt
              (__str_mk_re_loop_elim_rec (zeroList len) a
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a)
                  (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start)))) =
            SmtValue.RegLan
              (nativeLoopRaw len rv (native_re_concat rv (nativeRePow start rv))) := by
        rw [← hStartSucc]
        exact re_loop_elim_raw_rec_eval_eq M a rv haTy haEval len (Nat.succ start)
      have hTailNe :
          __str_mk_re_loop_elim_rec (zeroList len) a
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a)
              (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start)) ≠
            Term.Stuck :=
        term_ne_stuck_of_eval_reglan M _ _ hTailEval
      have hTailNotNil :
          __eo_is_list_nil (Term.UOp UserOp.re_union)
            (__str_mk_re_loop_elim_rec (zeroList len) a
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a)
                (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start))) =
            Term.Boolean false := by
        rw [← hStartSucc]
        exact re_loop_elim_raw_rec_not_nil M a rv haTy haEval len (Nat.succ start)
      have hElim2 :
          __eo_list_singleton_elim_2
            (__str_mk_re_loop_elim_rec (zeroList (Nat.succ len)) a
              (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start)) =
          __str_mk_re_loop_elim_rec (zeroList (Nat.succ len)) a
            (__eo_list_repeat_rec (Term.UOp UserOp.re_concat) a start) := by
        simp [zeroList, __str_mk_re_loop_elim_rec]
        rw [eo_mk_apply_of_ne_stuck (by intro h; cases h) hSingNe]
        rw [eo_mk_apply_of_ne_stuck (re_union_apply_head_ne_stuck _) hTailNe]
        simp [__eo_list_singleton_elim_2, hTailNotNil, __eo_ite,
          native_ite, native_teq]
      rw [hElim2]
      exact hRawEval

private theorem re_list_repeat_numeral_eq_rec
    (a : Term) (i : native_Int)
    (hi : 0 ≤ i)
    (haNe : a ≠ Term.Stuck) :
    __eo_list_repeat (Term.UOp UserOp.re_concat) a (Term.Numeral i) =
      __eo_list_repeat_rec (Term.UOp UserOp.re_concat) a
        (native_int_to_nat i) := by
  have hNonneg : native_zlt i 0 = false := by
    simp [native_zlt]
    omega
  cases a <;> simp [__eo_list_repeat, native_ite, hNonneg] at haNe ⊢

private theorem typed_zero_list_repeat_numeral_eq
    (i : native_Int) (hi : 0 ≤ i) :
    __eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
        (Term.Numeral 0) (Term.Numeral i) =
      zeroList (native_int_to_nat i) := by
  have hNonneg : native_zlt i 0 = false := by
    simp [native_zlt]
    omega
  simp [__eo_list_repeat, native_ite, hNonneg,
    typed_zero_list_repeat_rec_eq]

private theorem int_to_nat_sub_add
    (lo hi : native_Int)
    (hlo : 0 ≤ lo)
    (hdiff : 0 ≤ hi - lo) :
    lo + Int.ofNat (native_int_to_nat (hi - lo)) = hi := by
  dsimp [native_int_to_nat]
  change lo + (↑(Int.toNat (hi - lo)) : Int) = hi
  rw [Int.toNat_of_nonneg hdiff]
  change lo + (hi + -lo) = hi
  rw [← Int.add_assoc]
  rw [Int.add_comm lo hi]
  rw [Int.add_assoc]
  rw [Int.add_right_neg]
  rw [Int.add_zero]

theorem re_loop_elim_eval_rel
    (M : SmtModel) (lo hi : native_Int) (a : Term) (rv : SmtRegLan)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (haEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan rv)
    (hlo : 0 ≤ lo)
    (hdiff : 0 ≤ hi - lo) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (__eo_list_singleton_elim (Term.UOp UserOp.re_union)
            (__str_mk_re_loop_elim_rec
              (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
                (Term.Numeral 0)
                (Term.Numeral (native_zplus (native_zneg lo) hi)))
              a
              (__eo_list_repeat (Term.UOp UserOp.re_concat) a
                (Term.Numeral lo))))))
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp2 UserOp2.re_loop (Term.Numeral lo)
            (Term.Numeral hi)) a))) := by
  let diff : native_Int := hi - lo
  let diffNat : native_Nat := native_int_to_nat diff
  have hDiffExpr : native_zplus (native_zneg lo) hi = diff := by
    dsimp [diff]
    change -lo + hi = hi + -lo
    rw [Int.add_comm]
  have hDiffNonneg : 0 ≤ diff := by
    simpa [diff] using hdiff
  have hANe := term_ne_stuck_of_smt_reglan a haTy
  have hRepeatR :
      __eo_list_repeat (Term.UOp UserOp.re_concat) a (Term.Numeral lo) =
        __eo_list_repeat_rec (Term.UOp UserOp.re_concat) a
          (native_int_to_nat lo) :=
    re_list_repeat_numeral_eq_rec a lo hlo hANe
  have hRepeatZeros :
      __eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0)
          (Term.Numeral (native_zplus (native_zneg lo) hi)) =
        zeroList diffNat := by
    rw [hDiffExpr]
    exact typed_zero_list_repeat_numeral_eq diff hDiffNonneg
  have hExpandedEval :
      __smtx_model_eval M
        (__eo_to_smt
          (__eo_list_singleton_elim (Term.UOp UserOp.re_union)
            (__str_mk_re_loop_elim_rec
              (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
                (Term.Numeral 0)
                (Term.Numeral (native_zplus (native_zneg lo) hi)))
              a
              (__eo_list_repeat (Term.UOp UserOp.re_concat) a
                (Term.Numeral lo))))) =
        SmtValue.RegLan
          (nativeLoopOuter diffNat rv
            (nativeRePow (native_int_to_nat lo) rv)) := by
    rw [hRepeatZeros, hRepeatR]
    exact re_loop_elim_outer_eval_eq M a rv haTy haEval diffNat
      (native_int_to_nat lo)
  have hLt : native_zlt hi lo = false := by
    have hle : lo ≤ hi := (Int.sub_nonneg.mp hdiff)
    have hltFalse : ¬ hi < lo := (Int.not_lt).mpr hle
    simp [native_zlt, hltFalse]
  have hHiEq : lo + Int.ofNat diffNat = hi := by
    dsimp [diffNat, diff]
    exact int_to_nat_sub_add lo hi hlo hdiff
  have hLoopEval :
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp2 UserOp2.re_loop (Term.Numeral lo)
            (Term.Numeral hi)) a)) =
        SmtValue.RegLan (nativeReLoopRec diffNat lo hi rv) := by
    have hLoopDiff : native_zplus hi (native_zneg lo) = diff := by
      dsimp [diff]
      change hi + -lo = hi + -lo
      rfl
    change __smtx_model_eval M
        (SmtTerm.re_loop (SmtTerm.Numeral lo) (SmtTerm.Numeral hi)
          (__eo_to_smt a)) =
      SmtValue.RegLan (nativeReLoopRec diffNat lo hi rv)
    rw [__smtx_model_eval.eq_118, __smtx_model_eval.eq_2,
      __smtx_model_eval.eq_2, haEval]
    simp [__smtx_model_eval_re_loop, __smtx_model_eval_gt,
      __smtx_model_eval_lt, __smtx_model_eval_ite, hLt, diffNat, diff,
      hLoopDiff, model_eval_re_loop_rec_reglan_eq]
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  rw [hExpandedEval, hLoopEval]
  change
    __smtx_model_eval_eq
      (SmtValue.RegLan
        (nativeLoopOuter diffNat rv (nativeRePow (native_int_to_nat lo) rv)))
      (SmtValue.RegLan (nativeReLoopRec diffNat lo hi rv)) =
      SmtValue.Boolean true
  change
    SmtValue.Boolean
      (native_re_ext_eq
        (nativeLoopOuter diffNat rv (nativeRePow (native_int_to_nat lo) rv))
        (nativeReLoopRec diffNat lo hi rv)) =
      SmtValue.Boolean true
  simp
  intro str hValid
  calc
    native_str_in_re str
        (nativeLoopOuter diffNat rv (nativeRePow (native_int_to_nat lo) rv))
        =
      native_str_in_re str
        (nativeLoopElim diffNat rv (nativeRePow (native_int_to_nat lo) rv)) := by
        exact nativeLoopOuter_elim_ext diffNat rv
          (nativeRePow (native_int_to_nat lo) rv) str hValid
    _ =
      native_str_in_re str
        (nativeRangeRight (native_int_to_nat lo) diffNat rv) := by
        exact nativeLoopElim_range_ext diffNat (native_int_to_nat lo) rv str
          hValid
    _ =
      native_str_in_re str (nativeReLoopRec diffNat lo hi rv) := by
        rw [← hHiEq]
        exact (nativeReLoopRec_range_ext diffNat lo rv str hlo hValid).symm
