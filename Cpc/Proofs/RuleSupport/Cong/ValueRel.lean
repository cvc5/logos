module

public import Cpc.Proofs.RuleSupport.Cong.Core
import all Cpc.Proofs.RuleSupport.Cong.Core
public import Cpc.Proofs.Translation.Apply
import all Cpc.Proofs.Translation.Apply
import all Cpc.SmtModel

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace CongSupport

attribute [local simp] native_streq native_and native_ite

private theorem native_list_in_re_raw_star_congr :
    (xs : List native_Char) -> (r r' : SmtRegLan) ->
      (∀ ys : List native_Char,
        native_list_in_re ys r = native_list_in_re ys r') ->
      native_list_in_re xs (SmtRegLan.star r) =
        native_list_in_re xs (SmtRegLan.star r')
  | [], r, r', _hExt => by
      rfl
  | c :: cs, r, r', hExt => by
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro h
        have hConcat :
            native_list_in_re cs
                (native_re_mk_concat (native_re_deriv c r)
                  (SmtRegLan.star r)) = true := by
          exact h
        rcases
            (native_list_in_re_mk_concat_true_iff_exists_append cs
              (native_re_deriv c r) (SmtRegLan.star r)).1 hConcat with
          ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
        have hLeft' :
            native_list_in_re xs₁ (native_re_deriv c r') = true := by
          have hDeriv :
              native_list_in_re xs₁ (native_re_deriv c r) =
                native_list_in_re xs₁ (native_re_deriv c r') := by
            exact hExt (c :: xs₁)
          rw [← hDeriv]
          exact hLeft
        have hLen : xs₂.length < (c :: cs).length := by
          have hLenEq := congrArg List.length hAppend
          simp at hLenEq ⊢
          omega
        have hRight' :
            native_list_in_re xs₂ (SmtRegLan.star r') = true := by
          have hStar :=
            native_list_in_re_raw_star_congr xs₂ r r' hExt
          rw [← hStar]
          exact hRight
        have hConcat' :
            native_list_in_re cs
                (native_re_mk_concat (native_re_deriv c r')
                  (SmtRegLan.star r')) = true :=
          (native_list_in_re_mk_concat_true_iff_exists_append cs
            (native_re_deriv c r') (SmtRegLan.star r')).2
            ⟨xs₁, xs₂, hAppend, hLeft', hRight'⟩
        exact hConcat'
      · intro h
        have hConcat :
            native_list_in_re cs
                (native_re_mk_concat (native_re_deriv c r')
                  (SmtRegLan.star r')) = true := by
          exact h
        rcases
            (native_list_in_re_mk_concat_true_iff_exists_append cs
              (native_re_deriv c r') (SmtRegLan.star r')).1 hConcat with
          ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
        have hLeft' :
            native_list_in_re xs₁ (native_re_deriv c r) = true := by
          have hDeriv :
              native_list_in_re xs₁ (native_re_deriv c r) =
                native_list_in_re xs₁ (native_re_deriv c r') := by
            exact hExt (c :: xs₁)
          rw [hDeriv]
          exact hLeft
        have hLen : xs₂.length < (c :: cs).length := by
          have hLenEq := congrArg List.length hAppend
          simp at hLenEq ⊢
          omega
        have hRight' :
            native_list_in_re xs₂ (SmtRegLan.star r) = true := by
          have hStar :=
            native_list_in_re_raw_star_congr xs₂ r r' hExt
          rw [hStar]
          exact hRight
        have hConcat' :
            native_list_in_re cs
                (native_re_mk_concat (native_re_deriv c r)
                  (SmtRegLan.star r)) = true :=
          (native_list_in_re_mk_concat_true_iff_exists_append cs
            (native_re_deriv c r) (SmtRegLan.star r)).2
            ⟨xs₁, xs₂, hAppend, hLeft', hRight'⟩
        exact hConcat'
termination_by xs _ _ _ => xs.length
decreasing_by
  all_goals
    omega

private theorem native_list_in_re_raw_star_append :
    (xs ys : List native_Char) -> (r : SmtRegLan) ->
      native_list_in_re xs (SmtRegLan.star r) = true ->
      native_list_in_re ys (SmtRegLan.star r) = true ->
      native_list_in_re (xs ++ ys) (SmtRegLan.star r) = true
  | [], ys, r, _hLeft, hRight => by
      simpa using hRight
  | c :: cs, ys, r, hLeft, hRight => by
      have hConcat :
          native_list_in_re cs
              (native_re_mk_concat (native_re_deriv c r)
                (SmtRegLan.star r)) = true := by
        exact hLeft
      rcases
          (native_list_in_re_mk_concat_true_iff_exists_append cs
            (native_re_deriv c r) (SmtRegLan.star r)).1 hConcat with
        ⟨xs₁, xs₂, hAppend, hChunk, hTail⟩
      have hLen : xs₂.length < (c :: cs).length := by
        have hLenEq := congrArg List.length hAppend
        simp at hLenEq ⊢
        omega
      have hTailAppend :
          native_list_in_re (xs₂ ++ ys) (SmtRegLan.star r) = true :=
        native_list_in_re_raw_star_append xs₂ ys r hTail hRight
      have hAppend' : xs₁ ++ (xs₂ ++ ys) = cs ++ ys := by
        rw [← List.append_assoc, hAppend]
      have hConcat' :
          native_list_in_re (cs ++ ys)
              (native_re_mk_concat (native_re_deriv c r)
                (SmtRegLan.star r)) = true :=
        (native_list_in_re_mk_concat_true_iff_exists_append (cs ++ ys)
          (native_re_deriv c r) (SmtRegLan.star r)).2
          ⟨xs₁, xs₂ ++ ys, hAppend', hChunk, hTailAppend⟩
      exact hConcat'
termination_by xs _ _ _ _ => xs.length
decreasing_by
  all_goals
    omega

private theorem native_list_in_re_raw_star_star :
    (xs : List native_Char) -> (r : SmtRegLan) ->
      native_list_in_re xs (SmtRegLan.star (SmtRegLan.star r)) =
        native_list_in_re xs (SmtRegLan.star r)
  | [], r => by
      rfl
  | c :: cs, r => by
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro h
        have hConcat :
            native_list_in_re cs
                (native_re_mk_concat
                  (native_re_deriv c (SmtRegLan.star r))
                  (SmtRegLan.star (SmtRegLan.star r))) = true := by
          exact h
        rcases
            (native_list_in_re_mk_concat_true_iff_exists_append cs
              (native_re_deriv c (SmtRegLan.star r))
              (SmtRegLan.star (SmtRegLan.star r))).1 hConcat with
          ⟨xs₁, xs₂, hAppend, hChunk, hTail⟩
        have hChunkStar :
            native_list_in_re (c :: xs₁) (SmtRegLan.star r) = true := by
          exact hChunk
        have hTailStar :
            native_list_in_re xs₂ (SmtRegLan.star r) = true := by
          have hTailEq := native_list_in_re_raw_star_star xs₂ r
          rw [← hTailEq]
          exact hTail
        have hJoin :
            native_list_in_re ((c :: xs₁) ++ xs₂)
                (SmtRegLan.star r) = true :=
          native_list_in_re_raw_star_append (c :: xs₁) xs₂ r
            hChunkStar hTailStar
        simpa [hAppend] using hJoin
      · intro h
        have hDeriv :
            native_list_in_re cs
                (native_re_deriv c (SmtRegLan.star r)) = true := by
          exact h
        have hNil :
            native_list_in_re [] (SmtRegLan.star (SmtRegLan.star r)) =
              true := by
          rfl
        have hConcat :
            native_list_in_re cs
                (native_re_mk_concat
                  (native_re_deriv c (SmtRegLan.star r))
                  (SmtRegLan.star (SmtRegLan.star r))) = true :=
          (native_list_in_re_mk_concat_true_iff_exists_append cs
            (native_re_deriv c (SmtRegLan.star r))
            (SmtRegLan.star (SmtRegLan.star r))).2
            ⟨cs, [], by simp, hDeriv, hNil⟩
        exact hConcat
termination_by xs _ => xs.length
decreasing_by
  all_goals
    have hLenEq := congrArg List.length hAppend
    simp at hLenEq ⊢
    omega

private theorem native_list_in_re_mk_star_raw
    (xs : List native_Char) (r : SmtRegLan) :
    native_list_in_re xs (native_re_mk_star r) =
      native_list_in_re xs (SmtRegLan.star r) := by
  cases r <;> try rfl
  · cases xs <;> simp [native_re_mk_star, native_re_mult,
      native_list_in_re, RuleProofs.nativeListInRe, native_re_nullable,
      native_re_deriv, native_re_concat]
  · cases xs <;> simp [native_re_mk_star, native_re_mult,
      native_list_in_re, RuleProofs.nativeListInRe, native_re_nullable,
      native_re_deriv, native_re_concat]
  · exact (native_list_in_re_raw_star_star xs _).symm

private theorem native_list_in_re_raw_star_congr_valid :
    (xs : List native_Char) -> (r r' : SmtRegLan) ->
      native_string_valid xs = true ->
      (∀ ys : List native_Char,
        native_string_valid ys = true ->
          native_list_in_re ys r = native_list_in_re ys r') ->
      native_list_in_re xs (SmtRegLan.star r) =
        native_list_in_re xs (SmtRegLan.star r')
  | [], r, r', _hValid, _hExt => by
      rfl
  | c :: cs, r, r', hValid, hExt => by
      have hc : native_char_valid c = true :=
        (native_string_valid_cons_parts hValid).1
      have hcs : native_string_valid cs = true :=
        (native_string_valid_cons_parts hValid).2
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro h
        have hConcat :
            native_list_in_re cs
                (native_re_mk_concat (native_re_deriv c r)
                  (SmtRegLan.star r)) = true := by
          exact h
        rcases
            (native_list_in_re_mk_concat_true_iff_exists_append cs
              (native_re_deriv c r) (SmtRegLan.star r)).1 hConcat with
          ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
        have hAppendValid : native_string_valid (xs₁ ++ xs₂) = true := by
          rw [hAppend]
          exact hcs
        have hValid₁ := native_string_valid_append_left xs₁ xs₂ hAppendValid
        have hValid₂ := native_string_valid_append_right xs₁ xs₂ hAppendValid
        have hLeft' :
            native_list_in_re xs₁ (native_re_deriv c r') = true := by
          have hDeriv :
              native_list_in_re xs₁ (native_re_deriv c r) =
                native_list_in_re xs₁ (native_re_deriv c r') := by
            exact hExt (c :: xs₁) (native_string_valid_cons hc hValid₁)
          rw [← hDeriv]
          exact hLeft
        have hRight' :
            native_list_in_re xs₂ (SmtRegLan.star r') = true := by
          have hStar :=
            native_list_in_re_raw_star_congr_valid xs₂ r r' hValid₂ hExt
          rw [← hStar]
          exact hRight
        have hConcat' :
            native_list_in_re cs
                (native_re_mk_concat (native_re_deriv c r')
                  (SmtRegLan.star r')) = true :=
          (native_list_in_re_mk_concat_true_iff_exists_append cs
            (native_re_deriv c r') (SmtRegLan.star r')).2
            ⟨xs₁, xs₂, hAppend, hLeft', hRight'⟩
        exact hConcat'
      · intro h
        have hConcat :
            native_list_in_re cs
                (native_re_mk_concat (native_re_deriv c r')
                  (SmtRegLan.star r')) = true := by
          exact h
        rcases
            (native_list_in_re_mk_concat_true_iff_exists_append cs
              (native_re_deriv c r') (SmtRegLan.star r')).1 hConcat with
          ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
        have hAppendValid : native_string_valid (xs₁ ++ xs₂) = true := by
          rw [hAppend]
          exact hcs
        have hValid₁ := native_string_valid_append_left xs₁ xs₂ hAppendValid
        have hValid₂ := native_string_valid_append_right xs₁ xs₂ hAppendValid
        have hLeft' :
            native_list_in_re xs₁ (native_re_deriv c r) = true := by
          have hDeriv :
              native_list_in_re xs₁ (native_re_deriv c r) =
                native_list_in_re xs₁ (native_re_deriv c r') := by
            exact hExt (c :: xs₁) (native_string_valid_cons hc hValid₁)
          rw [hDeriv]
          exact hLeft
        have hRight' :
            native_list_in_re xs₂ (SmtRegLan.star r) = true := by
          have hStar :=
            native_list_in_re_raw_star_congr_valid xs₂ r r' hValid₂ hExt
          rw [hStar]
          exact hRight
        have hConcat' :
            native_list_in_re cs
                (native_re_mk_concat (native_re_deriv c r)
                  (SmtRegLan.star r)) = true :=
          (native_list_in_re_mk_concat_true_iff_exists_append cs
            (native_re_deriv c r) (SmtRegLan.star r)).2
            ⟨xs₁, xs₂, hAppend, hLeft', hRight'⟩
        exact hConcat'
termination_by xs _ _ _ _ => xs.length
decreasing_by
  all_goals
    have hLenEq := congrArg List.length hAppend
    simp at hLenEq ⊢
    omega

private theorem native_list_in_re_mk_star_congr_valid
    (xs : List native_Char) (r r' : SmtRegLan)
    (hValid : native_string_valid xs = true)
    (hExt :
      ∀ ys : List native_Char,
        native_string_valid ys = true ->
          native_list_in_re ys r = native_list_in_re ys r') :
    native_list_in_re xs (native_re_mk_star r) =
      native_list_in_re xs (native_re_mk_star r') := by
  rw [native_list_in_re_mk_star_raw xs r,
    native_list_in_re_mk_star_raw xs r']
  exact native_list_in_re_raw_star_congr_valid xs r r' hValid hExt

theorem native_str_in_re_re_mult_congr
    (str : native_String) (r r' : SmtRegLan)
    (hExt :
      ∀ s : native_String,
        native_string_valid s = true ->
          native_str_in_re s r = native_str_in_re s r') :
    native_str_in_re str (native_re_mult r) =
      native_str_in_re str (native_re_mult r') := by
  by_cases hValid : native_string_valid str = true
  · have hList :
        ∀ ys : List native_Char,
          native_string_valid ys = true ->
            native_list_in_re ys r = native_list_in_re ys r' := by
      intro ys hys
      simpa [native_str_in_re, native_list_in_re, hys] using
        hExt ys hys
    simpa [native_str_in_re, hValid, native_re_mult, native_re_mk_star] using
      native_list_in_re_mk_star_congr_valid str r r' hValid hList
  · have hInvalid : native_string_valid str = false := by
      cases h : native_string_valid str <;> simp [h] at hValid ⊢
    simp [native_str_in_re, hInvalid]

theorem native_str_in_re_re_plus_congr
    (str : native_String) (r r' : SmtRegLan)
    (hExt :
      ∀ s : native_String,
        native_string_valid s = true ->
          native_str_in_re s r = native_str_in_re s r') :
    native_str_in_re str (native_re_plus r) =
      native_str_in_re str (native_re_plus r') := by
  have hStar :
    ∀ s : native_String,
        native_string_valid s = true ->
          native_str_in_re s (native_re_mult r) =
          native_str_in_re s (native_re_mult r') := by
    intro s _hs
    exact native_str_in_re_re_mult_congr s r r' hExt
  exact native_str_in_re_re_concat_congr str r r' (native_re_mk_star r) (native_re_mk_star r') hExt hStar

private theorem native_list_in_re_deriv_congr_valid
    (c : native_Char) (r r' : SmtRegLan)
    (hc : native_char_valid c = true)
    (hExt :
      ∀ ys : List native_Char,
        native_string_valid ys = true ->
          native_list_in_re ys r = native_list_in_re ys r') :
    ∀ ys : List native_Char,
      native_string_valid ys = true ->
        native_list_in_re ys (native_re_deriv c r) =
          native_list_in_re ys (native_re_deriv c r') := by
  intro ys hys
  exact hExt (c :: ys) (native_string_valid_cons hc hys)

private theorem native_re_prefix_match_len_go_congr_valid :
    ∀ (xs : List native_Char) (r r' : SmtRegLan) (n : Nat),
      native_string_valid xs = true ->
      (∀ ys : List native_Char,
        native_string_valid ys = true ->
          native_list_in_re ys r = native_list_in_re ys r') ->
      impl_native_re_prefix_match_len_go r (impl_native_string_to_values xs) n =
        impl_native_re_prefix_match_len_go r' (impl_native_string_to_values xs) n := by
  intro xs
  induction xs with
  | nil =>
      intro r r' n _hValid hExt
      have hNull : native_re_nullable r = native_re_nullable r' := by
        exact hExt [] (by simp [native_string_valid])
      simp [impl_native_string_to_values, impl_native_re_prefix_match_len_go, hNull]
  | cons c cs ih =>
      intro r r' n hValid hExt
      have hc : native_char_valid c = true :=
        (native_string_valid_cons_parts hValid).1
      have hcs : native_string_valid cs = true :=
        (native_string_valid_cons_parts hValid).2
      have hNull : native_re_nullable r = native_re_nullable r' := by
        exact hExt [] (by simp [native_string_valid])
      by_cases hR : native_re_nullable r = true
      · have hRp : native_re_nullable r' = true := by
          simpa [← hNull] using hR
        simp [impl_native_string_to_values, impl_native_re_prefix_match_len_go, hR, hRp]
      · have hRfalse : native_re_nullable r = false := by
          cases hVal : native_re_nullable r with
          | false => rfl
          | true => exact False.elim (hR hVal)
        have hRpfalse : native_re_nullable r' = false := by
          simpa [← hNull] using hRfalse
        simp [impl_native_string_to_values, impl_native_re_prefix_match_len_go,
          hRfalse, hRpfalse]
        exact ih (native_re_deriv c r) (native_re_deriv c r') (n + 1)
          hcs (native_list_in_re_deriv_congr_valid c r r' hc hExt)

private theorem native_re_prefix_match_len_congr_valid
    (r r' : SmtRegLan) (xs : List native_Char)
    (hValid : native_string_valid xs = true)
    (hExt :
      ∀ ys : List native_Char,
        native_string_valid ys = true ->
          native_list_in_re ys r = native_list_in_re ys r') :
    native_re_prefix_match_len? r (impl_native_string_to_values xs) =
      native_re_prefix_match_len? r' (impl_native_string_to_values xs) := by
  unfold native_re_prefix_match_len?
  exact native_re_prefix_match_len_go_congr_valid xs r r' 0 hValid hExt

private theorem native_re_positive_prefix_match_len_congr_valid
    (r r' : SmtRegLan) (xs : List native_Char)
    (hValid : native_string_valid xs = true)
    (hExt :
      ∀ ys : List native_Char,
        native_string_valid ys = true ->
          native_list_in_re ys r = native_list_in_re ys r') :
    native_re_positive_prefix_match_len? r (impl_native_string_to_values xs) =
      native_re_positive_prefix_match_len? r' (impl_native_string_to_values xs) := by
  cases xs with
  | nil =>
      rfl
  | cons c cs =>
      have hc : native_char_valid c = true :=
        (native_string_valid_cons_parts hValid).1
      have hcs : native_string_valid cs = true :=
        (native_string_valid_cons_parts hValid).2
      have hPref := native_re_prefix_match_len_congr_valid
        (native_re_deriv c r) (native_re_deriv c r') cs hcs
        (native_list_in_re_deriv_congr_valid c r r' hc hExt)
      have hPref' :
          native_re_prefix_match_len? (native_re_deriv c r)
              (List.map SmtValue.Char cs) =
            native_re_prefix_match_len? (native_re_deriv c r')
              (List.map SmtValue.Char cs) := by
        simpa [impl_native_string_to_values] using hPref
      simp only [impl_native_string_to_values, List.map,
        native_re_positive_prefix_match_len?]
      rw [hPref']

private theorem native_re_find_idx_aux_congr_valid :
    ∀ (xs : List native_Char) (idx : Nat) (r r' : SmtRegLan),
      native_string_valid xs = true ->
      (∀ ys : List native_Char,
        native_string_valid ys = true ->
          native_list_in_re ys r = native_list_in_re ys r') ->
      impl_native_re_find_idx_aux r (impl_native_string_to_values xs) idx =
        impl_native_re_find_idx_aux r' (impl_native_string_to_values xs) idx := by
  intro xs
  induction xs with
  | nil =>
      intro idx r r' hValid hExt
      simp only [impl_native_string_to_values, List.map]
      have hPref :
          native_re_prefix_match_len? r [] =
            native_re_prefix_match_len? r' [] := by
        simpa [impl_native_string_to_values] using
          native_re_prefix_match_len_congr_valid r r' [] hValid hExt
      rw [impl_native_re_find_idx_aux.eq_def, impl_native_re_find_idx_aux.eq_def, hPref]
  | cons c cs ih =>
      intro idx r r' hValid hExt
      have hcs : native_string_valid cs = true :=
        (native_string_valid_cons_parts hValid).2
      simp only [impl_native_string_to_values, List.map]
      have hPref :
          native_re_prefix_match_len? r (SmtValue.Char c :: List.map SmtValue.Char cs) =
            native_re_prefix_match_len? r'
              (SmtValue.Char c :: List.map SmtValue.Char cs) := by
        simpa [impl_native_string_to_values] using
          native_re_prefix_match_len_congr_valid r r' (c :: cs) hValid hExt
      rw [impl_native_re_find_idx_aux.eq_def, impl_native_re_find_idx_aux.eq_def, hPref]
      cases native_re_prefix_match_len? r'
          (SmtValue.Char c :: List.map SmtValue.Char cs) with
      | none => exact ih (idx + 1) r r' hcs hExt
      | some _ => rfl

private theorem native_re_find_idx_from_congr_valid
    (r r' : SmtRegLan) (xs : List native_Char) (start : Nat)
    (hValid : native_string_valid xs = true)
    (hExt :
      ∀ ys : List native_Char,
        native_string_valid ys = true ->
          native_list_in_re ys r = native_list_in_re ys r') :
    native_re_find_idx_from r (impl_native_string_to_values xs) start =
      native_re_find_idx_from r' (impl_native_string_to_values xs) start := by
  simpa [native_re_find_idx_from, impl_native_string_to_values] using
    native_re_find_idx_aux_congr_valid (xs.drop start) start r r'
      (native_string_valid_drop xs start hValid) hExt

private theorem native_re_replace_all_nonempty_list_aux_congr_valid :
    ∀ (fuel : Nat) (xs replacement : List native_Char) (r r' : SmtRegLan),
      native_string_valid xs = true ->
      (∀ ys : List native_Char,
        native_string_valid ys = true ->
          native_list_in_re ys r = native_list_in_re ys r') ->
      impl_native_re_replace_all_nonempty_list_aux fuel r
          (impl_native_string_to_values replacement) (impl_native_string_to_values xs) =
        impl_native_re_replace_all_nonempty_list_aux fuel r'
          (impl_native_string_to_values replacement) (impl_native_string_to_values xs) := by
  intro fuel
  induction fuel with
  | zero =>
      intro xs replacement r r' hValid hExt
      rfl
  | succ fuel ih =>
      intro xs replacement r r' hValid hExt
      cases xs with
      | nil =>
          simp only [impl_native_string_to_values, List.map]
          have hPref :
              native_re_positive_prefix_match_len? r [] =
                native_re_positive_prefix_match_len? r' [] := by
            simpa [impl_native_string_to_values] using
              native_re_positive_prefix_match_len_congr_valid r r' []
                (by simp [native_string_valid]) hExt
          rw [impl_native_re_replace_all_nonempty_list_aux.eq_2,
            impl_native_re_replace_all_nonempty_list_aux.eq_2, hPref]
          cases native_re_positive_prefix_match_len? r' [] with
          | none => rfl
          | some n =>
              cases n with
              | zero => rfl
              | succ n =>
                  simp
                  exact ih [] replacement r r' (by simp [native_string_valid]) hExt
      | cons c cs =>
          have hcs : native_string_valid cs = true :=
            (native_string_valid_cons_parts hValid).2
          simp only [impl_native_string_to_values, List.map]
          have hPref :
              native_re_positive_prefix_match_len? r
                  (SmtValue.Char c :: List.map SmtValue.Char cs) =
                native_re_positive_prefix_match_len? r'
                  (SmtValue.Char c :: List.map SmtValue.Char cs) := by
            simpa [impl_native_string_to_values] using
              native_re_positive_prefix_match_len_congr_valid r r'
                (c :: cs) hValid hExt
          rw [impl_native_re_replace_all_nonempty_list_aux.eq_3,
            impl_native_re_replace_all_nonempty_list_aux.eq_3, hPref]
          cases native_re_positive_prefix_match_len? r'
              (SmtValue.Char c :: List.map SmtValue.Char cs) with
          | none =>
              simp only [List.cons.injEq, true_and]
              have hIH := ih cs replacement r r' hcs hExt
              simpa [impl_native_string_to_values] using
                congrArg (fun tail => SmtValue.Char c :: tail) hIH
          | some n =>
              cases n with
              | zero =>
                  simp only [List.cons.injEq, true_and]
                  have hIH := ih cs replacement r r' hcs hExt
                  simpa [impl_native_string_to_values] using
                    congrArg (fun tail => SmtValue.Char c :: tail) hIH
              | succ n =>
                  simp
                  simpa [impl_native_string_to_values] using
                    ih (List.drop n cs) replacement r r'
                      (native_string_valid_drop cs n hcs) hExt

private theorem native_re_replace_all_nonempty_list_congr_valid
    (r r' : SmtRegLan) (replacement xs : List native_Char)
    (hValid : native_string_valid xs = true)
    (hExt :
      ∀ ys : List native_Char,
        native_string_valid ys = true ->
          native_list_in_re ys r = native_list_in_re ys r') :
    impl_native_re_replace_all_nonempty_list r (impl_native_string_to_values replacement)
        (impl_native_string_to_values xs) =
      impl_native_re_replace_all_nonempty_list r' (impl_native_string_to_values replacement)
        (impl_native_string_to_values xs) := by
  simpa [impl_native_re_replace_all_nonempty_list, impl_native_string_to_values] using
    native_re_replace_all_nonempty_list_aux_congr_valid
      (xs.length + 1) xs replacement r r' hValid hExt

private theorem native_str_ext_to_list_ext
    (r r' : SmtRegLan)
    (hExt :
      ∀ str : native_String,
        native_string_valid str = true ->
          native_str_in_re str r = native_str_in_re str r') :
    ∀ ys : List native_Char,
      native_string_valid ys = true ->
      native_list_in_re ys r = native_list_in_re ys r' := by
  intro ys hys
  simpa [native_str_in_re, native_list_in_re, hys] using hExt ys hys

end CongSupport
end

open Eo
open SmtEval
open Smtm

namespace CongSupport

theorem native_re_prefix_match_len_go_congr_valid_ext_of_str_ext
    (xs : List native_Char) (r r' : SmtRegLan) (n : Nat)
    (hValid : native_string_valid xs = true)
    (hExt :
      ∀ ys : native_String,
        native_string_valid ys = true ->
          native_str_in_re ys r = native_str_in_re ys r') :
    impl_native_re_prefix_match_len_go r (impl_native_string_to_values xs) n =
      impl_native_re_prefix_match_len_go r' (impl_native_string_to_values xs) n :=
  native_re_prefix_match_len_go_congr_valid xs r r' n hValid
    (native_str_ext_to_list_ext r r' hExt)

end CongSupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace CongSupport

attribute [local simp] native_streq native_and native_ite

theorem native_str_in_re_ext_of_valid_ext
    {r r' : SmtRegLan}
    (hExt :
      ∀ str : native_String,
        native_string_valid str = true ->
          native_str_in_re str r = native_str_in_re str r') :
    ∀ str : native_String,
      native_str_in_re str r = native_str_in_re str r' := by
  intro str
  by_cases hValid : native_string_valid str = true
  · exact hExt str hValid
  · have hInvalid : native_string_valid str = false := by
      cases h : native_string_valid str <;> simp [h] at hValid ⊢
    simp [native_str_in_re, hInvalid]

theorem native_str_indexof_re_congr
    (s : native_String) (r r' : SmtRegLan) (i : native_Int)
    (hValid : native_string_valid s = true)
    (hExt :
      ∀ str : native_String,
        native_string_valid str = true ->
          native_str_in_re str r = native_str_in_re str r') :
    native_str_indexof_re (impl_native_string_to_values s) r i =
      native_str_indexof_re (impl_native_string_to_values s) r' i := by
  have hExtList := native_str_ext_to_list_ext r r' hExt
  by_cases hLt : i < 0
  · simp [native_str_indexof_re, hLt]
  · by_cases hStart : Int.toNat i ≤ s.length
    · have hStart' : Int.toNat i ≤ (impl_native_string_to_values s).length := by
        simpa [impl_native_string_to_values] using hStart
      simp only [native_str_indexof_re, if_neg hLt, if_pos hStart']
      rw [native_re_find_idx_from_congr_valid r r' s (Int.toNat i)
        hValid hExtList]
    · simp [native_str_indexof_re, impl_native_string_to_values, hLt, hStart]

private theorem native_model_str_in_re_congr
    (str : native_String) (r r' : SmtRegLan)
    (hExt : native_str_in_re str r = native_str_in_re str r') :
    Smtm.native_str_in_re (impl_native_string_to_values str) r =
      Smtm.native_str_in_re (impl_native_string_to_values str) r' := by
  rw [← RuleProofs.native_str_in_re_eq_model str r,
    ← RuleProofs.native_str_in_re_eq_model str r']
  simpa [native_str_in_re, RuleProofs.native_str_in_re] using hExt

private theorem native_str_indexof_re_split_aux_congr
    (r1 r1' r2 r2' : SmtRegLan)
    (hExt1 :
      ∀ str : native_String,
        native_str_in_re str r1 = native_str_in_re str r1')
    (hExt2 :
      ∀ str : native_String,
        native_str_in_re str r2 = native_str_in_re str r2') :
    ∀ (pre suf : native_String) i,
      impl_native_str_indexof_re_split_aux r1 r2
          (impl_native_string_to_values pre) (impl_native_string_to_values suf) i =
        impl_native_str_indexof_re_split_aux r1' r2'
          (impl_native_string_to_values pre) (impl_native_string_to_values suf) i := by
  intro pre suf
  induction suf generalizing pre with
  | nil =>
      intro i
      simp only [impl_native_string_to_values, List.map]
      change
        (if (Smtm.native_str_in_re (List.map SmtValue.Char pre) r1 &&
              Smtm.native_str_in_re [] r2) = true then Int.ofNat i else -1) =
          (if (Smtm.native_str_in_re (List.map SmtValue.Char pre) r1' &&
              Smtm.native_str_in_re [] r2') = true then Int.ofNat i else -1)
      have hPre :
          Smtm.native_str_in_re (List.map SmtValue.Char pre) r1 =
            Smtm.native_str_in_re (List.map SmtValue.Char pre) r1' := by
        simpa [impl_native_string_to_values] using
          native_model_str_in_re_congr pre r1 r1' (hExt1 pre)
      have hNil :
          Smtm.native_str_in_re [] r2 =
            Smtm.native_str_in_re [] r2' := by
        simpa [impl_native_string_to_values] using
          native_model_str_in_re_congr [] r2 r2' (hExt2 [])
      rw [hPre, hNil]
  | cons c cs ih =>
      intro i
      simp only [impl_native_string_to_values, List.map]
      change
        (if (Smtm.native_str_in_re (List.map SmtValue.Char pre) r1 &&
              Smtm.native_str_in_re
                (SmtValue.Char c :: List.map SmtValue.Char cs) r2) = true then
            Int.ofNat i
          else impl_native_str_indexof_re_split_aux r1 r2
            (List.map SmtValue.Char pre ++ [SmtValue.Char c])
            (List.map SmtValue.Char cs) (i + 1)) =
          (if (Smtm.native_str_in_re (List.map SmtValue.Char pre) r1' &&
                Smtm.native_str_in_re
                  (SmtValue.Char c :: List.map SmtValue.Char cs) r2') = true then
              Int.ofNat i
            else impl_native_str_indexof_re_split_aux r1' r2'
              (List.map SmtValue.Char pre ++ [SmtValue.Char c])
              (List.map SmtValue.Char cs) (i + 1))
      have hPre :
          Smtm.native_str_in_re (List.map SmtValue.Char pre) r1 =
            Smtm.native_str_in_re (List.map SmtValue.Char pre) r1' := by
        simpa [impl_native_string_to_values] using
          native_model_str_in_re_congr pre r1 r1' (hExt1 pre)
      have hSuf :
          Smtm.native_str_in_re
              (SmtValue.Char c :: List.map SmtValue.Char cs) r2 =
            Smtm.native_str_in_re
              (SmtValue.Char c :: List.map SmtValue.Char cs) r2' := by
        simpa [impl_native_string_to_values] using
          native_model_str_in_re_congr (c :: cs) r2 r2' (hExt2 (c :: cs))
      rw [hPre, hSuf]
      split
      · rfl
      · simpa [impl_native_string_to_values, List.map_append] using
          ih (pre ++ [c]) (i + 1)

theorem native_str_indexof_re_split_congr
    (s : native_String) (r1 r1' r2 r2' : SmtRegLan)
    (hExt1 :
      ∀ str : native_String,
        native_string_valid str = true ->
          native_str_in_re str r1 = native_str_in_re str r1')
    (hExt2 :
      ∀ str : native_String,
        native_string_valid str = true ->
          native_str_in_re str r2 = native_str_in_re str r2') :
    native_str_indexof_re_split (impl_native_string_to_values s) r1 r2 =
      native_str_indexof_re_split (impl_native_string_to_values s) r1' r2' := by
  have hExt1All := native_str_in_re_ext_of_valid_ext hExt1
  have hExt2All := native_str_in_re_ext_of_valid_ext hExt2
  simp only [native_str_indexof_re_split]
  rw [RuleProofs.native_re_str_valid_string]
  cases hValid : native_string_valid s
  · rfl
  · simpa [impl_native_string_to_values] using
      native_str_indexof_re_split_aux_congr r1 r1' r2 r2'
        hExt1All hExt2All [] s 0

theorem native_str_replace_re_congr
    (s : native_String) (r r' : SmtRegLan) (replacement : native_String)
    (hValid : native_string_valid s = true)
    (hExt :
      ∀ str : native_String,
        native_string_valid str = true ->
          native_str_in_re str r = native_str_in_re str r') :
    native_str_replace_re (impl_native_string_to_values s) r
        (impl_native_string_to_values replacement) =
      native_str_replace_re (impl_native_string_to_values s) r'
        (impl_native_string_to_values replacement) := by
  have hExtList := native_str_ext_to_list_ext r r' hExt
  simp only [native_str_replace_re]
  rw [native_re_find_idx_from_congr_valid r r' s 0 hValid hExtList]

private theorem native_re_find_nonempty_idx_aux_congr_valid :
    ∀ (xs : List native_Char) (idx : Nat) (r r' : SmtRegLan),
      native_string_valid xs = true ->
      (∀ ys : List native_Char,
        native_string_valid ys = true ->
          native_list_in_re ys r = native_list_in_re ys r') ->
      impl_native_re_find_nonempty_idx_aux r (impl_native_string_to_values xs) idx =
        impl_native_re_find_nonempty_idx_aux r' (impl_native_string_to_values xs) idx := by
  intro xs
  induction xs with
  | nil =>
      intro idx r r' hValid hExt
      simp only [impl_native_string_to_values, List.map]
      have hPref :
          native_re_positive_prefix_match_len? r [] =
            native_re_positive_prefix_match_len? r' [] := by
        simpa [impl_native_string_to_values] using
          native_re_positive_prefix_match_len_congr_valid r r' [] hValid hExt
      rw [impl_native_re_find_nonempty_idx_aux.eq_def,
        impl_native_re_find_nonempty_idx_aux.eq_def, hPref]
  | cons c cs ih =>
      intro idx r r' hValid hExt
      have hcs : native_string_valid cs = true :=
        (native_string_valid_cons_parts hValid).2
      simp only [impl_native_string_to_values, List.map]
      have hPref :
          native_re_positive_prefix_match_len? r
              (SmtValue.Char c :: List.map SmtValue.Char cs) =
            native_re_positive_prefix_match_len? r'
              (SmtValue.Char c :: List.map SmtValue.Char cs) := by
        simpa [impl_native_string_to_values] using
          native_re_positive_prefix_match_len_congr_valid r r' (c :: cs)
            hValid hExt
      rw [impl_native_re_find_nonempty_idx_aux.eq_def,
        impl_native_re_find_nonempty_idx_aux.eq_def, hPref]
      cases hRes : native_re_positive_prefix_match_len? r'
          (SmtValue.Char c :: List.map SmtValue.Char cs) with
      | none => exact ih (idx + 1) r r' hcs hExt
      | some n =>
          cases n with
          | zero => exact ih (idx + 1) r r' hcs hExt
          | succ n => rfl

private theorem native_re_find_nonempty_idx_from_congr_valid
    (r r' : SmtRegLan) (xs : List native_Char) (start : Nat)
    (hValid : native_string_valid xs = true)
    (hExt :
      ∀ ys : List native_Char,
        native_string_valid ys = true ->
          native_list_in_re ys r = native_list_in_re ys r') :
    impl_native_re_find_nonempty_idx_from r (impl_native_string_to_values xs) start =
      impl_native_re_find_nonempty_idx_from r' (impl_native_string_to_values xs) start := by
  simpa [impl_native_re_find_nonempty_idx_from, impl_native_string_to_values] using
    native_re_find_nonempty_idx_aux_congr_valid (xs.drop start) start r r'
      (native_string_valid_drop xs start hValid) hExt

private theorem native_re_scan_ends_aux_congr_valid :
    ∀ (fuel : Nat) (s : native_String) (pos : Nat) (r r' : SmtRegLan),
      native_string_valid s = true ->
      (∀ ys : List native_Char,
        native_string_valid ys = true ->
          native_list_in_re ys r = native_list_in_re ys r') ->
      impl_native_re_scan_ends_aux fuel r (impl_native_string_to_values s) pos =
        impl_native_re_scan_ends_aux fuel r' (impl_native_string_to_values s) pos := by
  intro fuel
  induction fuel with
  | zero =>
      intro s pos r r' hValid hExt
      rfl
  | succ fuel ih =>
      intro s pos r r' hValid hExt
      rw [impl_native_re_scan_ends_aux, impl_native_re_scan_ends_aux,
        native_re_find_nonempty_idx_from_congr_valid r r' s pos hValid hExt]
      cases impl_native_re_find_nonempty_idx_from r'
          (impl_native_string_to_values s) pos with
      | none => rfl
      | some p =>
          obtain ⟨idx, len⟩ := p
          simp only
          rw [ih s (idx + len) r r' hValid hExt]

/-- `@strings_occur_index_re` boundaries only depend on the language of the
regular expression. -/
theorem native_str_occur_index_re_congr
    (s : native_String) (r r' : SmtRegLan) (n : native_Int)
    (hValid : native_string_valid s = true)
    (hExt :
      ∀ str : native_String,
        native_string_valid str = true ->
          native_str_in_re str r = native_str_in_re str r') :
    native_str_occur_index_re (impl_native_string_to_values s) r n =
      native_str_occur_index_re (impl_native_string_to_values s) r' n := by
  have hExtList := native_str_ext_to_list_ext r r' hExt
  have hLength : (impl_native_string_to_values s).length = s.length := by
    simp [impl_native_string_to_values]
  simp only [native_str_occur_index_re]
  rw [hLength,
    native_re_scan_ends_aux_congr_valid (s.length + 1) s 0 r r' hValid
      hExtList]

theorem native_str_replace_re_all_congr
    (s : native_String) (r r' : SmtRegLan) (replacement : native_String)
    (hValid : native_string_valid s = true)
    (hExt :
      ∀ str : native_String,
        native_string_valid str = true ->
          native_str_in_re str r = native_str_in_re str r') :
    native_str_replace_re_all (impl_native_string_to_values s) r
        (impl_native_string_to_values replacement) =
      native_str_replace_re_all (impl_native_string_to_values s) r'
        (impl_native_string_to_values replacement) := by
  have hExtList := native_str_ext_to_list_ext r r' hExt
  simpa [native_str_replace_re_all] using
    native_re_replace_all_nonempty_list_congr_valid r r' replacement s hValid
      hExtList

theorem smt_value_rel_model_eval_eq_congr
    (a b c d : SmtValue) :
    RuleProofs.smt_value_rel a c ->
    RuleProofs.smt_value_rel b d ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_eq a b) (__smtx_model_eval_eq c d) := by
  intro hac hbd
  have hIff :
      RuleProofs.smt_value_rel a b ↔
        RuleProofs.smt_value_rel c d := by
    constructor
    · intro hab
      exact RuleProofs.smt_value_rel_trans c a d
        (RuleProofs.smt_value_rel_symm a c hac)
        (RuleProofs.smt_value_rel_trans a b d hab hbd)
    · intro hcd
      exact RuleProofs.smt_value_rel_trans a c b hac
        (RuleProofs.smt_value_rel_trans c d b hcd
          (RuleProofs.smt_value_rel_symm b d hbd))
  by_cases hab : RuleProofs.smt_value_rel a b
  · have hcd : RuleProofs.smt_value_rel c d := hIff.mp hab
    unfold RuleProofs.smt_value_rel at hab hcd ⊢
    rw [hab, hcd]
    simp [__smtx_model_eval_eq, native_veq]
  · have hncd : ¬ RuleProofs.smt_value_rel c d := by
      intro hcd
      exact hab (hIff.mpr hcd)
    have habFalse :
        __smtx_model_eval_eq a b = SmtValue.Boolean false :=
      smtx_model_eval_eq_false_of_not_smt_value_rel a b hab
    have hcdFalse :
        __smtx_model_eval_eq c d = SmtValue.Boolean false :=
      smtx_model_eval_eq_false_of_not_smt_value_rel c d hncd
    rw [habFalse, hcdFalse]
    simp [RuleProofs.smt_value_rel, __smtx_model_eval_eq, native_veq]

/--
SMT equality is congruent with respect to the project's semantic value relation.

This public wrapper is intentionally value-level: rules that reason about
substitution under equality can reuse the regex-extensional equality handling
without duplicating the operator proof.
-/
theorem smt_value_rel_eq_congr
    (a b c d : SmtValue) :
    RuleProofs.smt_value_rel a c ->
    RuleProofs.smt_value_rel b d ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_eq a b) (__smtx_model_eval_eq c d) :=
  smt_value_rel_model_eval_eq_congr a b c d

theorem congTrueSpine_eq_eq_true
    (M : SmtModel) (_hM : model_wf M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x₁) x₂) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_binary_uop_inv M UserOp.eq x₁ x₂ rhs hSpine with
    ⟨y₁, y₂, hRhs, hArg₁, hArg₂⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (SmtTerm.eq (__eo_to_smt x₁) (__eo_to_smt x₂)))
      (__smtx_model_eval M
        (SmtTerm.eq (__eo_to_smt y₁) (__eo_to_smt y₂)))
    rw [smtx_model_eval_eq_term_eq, smtx_model_eval_eq_term_eq]
    exact smt_value_rel_model_eval_eq_congr
      (__smtx_model_eval M (__eo_to_smt x₁))
      (__smtx_model_eval M (__eo_to_smt x₂))
      (__smtx_model_eval M (__eo_to_smt y₁))
      (__smtx_model_eval M (__eo_to_smt y₂))
      (smt_value_rel_of_eq_true_or_same M x₁ y₁ hArg₁)
      (smt_value_rel_of_eq_true_or_same M x₂ y₂ hArg₂)

theorem congTrueSpine_and_eq_true
    (M : SmtModel) (hM : model_wf M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.and) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.and) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.and) x₁) x₂) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_binary_uop_inv M UserOp.and x₁ x₂ rhs hSpine with
    ⟨y₁, y₂, hRhs, hArg₁, hArg₂⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) x₁) x₂)
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) y₁) y₂) hEqBool
    have hxAndNN :
        __smtx_typeof (SmtTerm.and (__eo_to_smt x₁) (__eo_to_smt x₂)) ≠
          SmtType.None := by
      simpa using hTypes.2
    rcases smt_typeof_and_args_bool_of_non_none
        (__eo_to_smt x₁) (__eo_to_smt x₂) hxAndNN with
      ⟨hx₁Bool, hx₂Bool⟩
    have hy₁Bool : __smtx_typeof (__eo_to_smt y₁) = SmtType.Bool := by
      rw [← smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁]
      exact hx₁Bool
    have hy₂Bool : __smtx_typeof (__eo_to_smt y₂) = SmtType.Bool := by
      rw [← smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂]
      exact hx₂Bool
    have hEval₁ :
        __smtx_model_eval M (__eo_to_smt x₁) =
          __smtx_model_eval M (__eo_to_smt y₁) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₁ y₁
        SmtType.Bool hx₁Bool hy₁Bool (by simp) (by simp) hArg₁
    have hEval₂ :
        __smtx_model_eval M (__eo_to_smt x₂) =
          __smtx_model_eval M (__eo_to_smt y₂) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₂ y₂
        SmtType.Bool hx₂Bool hy₂Bool (by simp) (by simp) hArg₂
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    change __smtx_model_eval_eq
      (__smtx_model_eval M
        (SmtTerm.and (__eo_to_smt x₁) (__eo_to_smt x₂)))
      (__smtx_model_eval M
        (SmtTerm.and (__eo_to_smt y₁) (__eo_to_smt y₂))) =
        SmtValue.Boolean true
    rw [__smtx_model_eval.eq_9, __smtx_model_eval.eq_9]
    rw [hEval₁, hEval₂]
    exact (RuleProofs.smt_value_rel_iff_model_eval_eq_true _ _).mp
      (RuleProofs.smt_value_rel_refl _)

theorem congTypeSpine_and_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.and) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.and) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.and) x₁) x₂) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_binary_uop_inv UserOp.and x₁ x₂ rhs hSpine with
    ⟨y₁, y₂, hRhs, hArg₁, hArg₂⟩
  subst hRhs
  have hxAndTy :
      __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) x₁) x₂)) =
        SmtType.Bool := by
    change __smtx_typeof (SmtTerm.and (__eo_to_smt x₁) (__eo_to_smt x₂)) =
      SmtType.Bool
    rcases smt_typeof_and_args_bool_of_non_none
        (__eo_to_smt x₁) (__eo_to_smt x₂) (by
          change __smtx_typeof
            (SmtTerm.and (__eo_to_smt x₁) (__eo_to_smt x₂)) ≠ SmtType.None
          exact hTrans) with
      ⟨hx₁Bool, hx₂Bool⟩
    rw [typeof_and_eq, hx₁Bool, hx₂Bool]
    simp [native_ite, native_Teq]
  have hx₁Bool : __smtx_typeof (__eo_to_smt x₁) = SmtType.Bool := by
    rcases smt_typeof_and_args_bool_of_non_none
        (__eo_to_smt x₁) (__eo_to_smt x₂) (by
          change __smtx_typeof
            (SmtTerm.and (__eo_to_smt x₁) (__eo_to_smt x₂)) ≠ SmtType.None
          exact hTrans) with
      ⟨h, _⟩
    exact h
  have hx₂Bool : __smtx_typeof (__eo_to_smt x₂) = SmtType.Bool := by
    rcases smt_typeof_and_args_bool_of_non_none
        (__eo_to_smt x₁) (__eo_to_smt x₂) (by
          change __smtx_typeof
            (SmtTerm.and (__eo_to_smt x₁) (__eo_to_smt x₂)) ≠ SmtType.None
          exact hTrans) with
      ⟨_, h⟩
    exact h
  have hy₁Bool : __smtx_typeof (__eo_to_smt y₁) = SmtType.Bool := by
    rw [← smt_type_eq_of_eq_bool_or_same x₁ y₁ hArg₁]
    exact hx₁Bool
  have hy₂Bool : __smtx_typeof (__eo_to_smt y₂) = SmtType.Bool := by
    rw [← smt_type_eq_of_eq_bool_or_same x₂ y₂ hArg₂]
    exact hx₂Bool
  have hyAndTy :
      __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) y₁) y₂)) =
        SmtType.Bool := by
    change __smtx_typeof (SmtTerm.and (__eo_to_smt y₁) (__eo_to_smt y₂)) =
      SmtType.Bool
    rw [typeof_and_eq, hy₁Bool, hy₂Bool]
    simp [native_ite, native_Teq]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply (Term.UOp UserOp.and) x₁) x₂)
    (Term.Apply (Term.Apply (Term.UOp UserOp.and) y₁) y₂)
    (by rw [hxAndTy, hyAndTy])
    (by rw [hxAndTy]; simp)

theorem congTrueSpine_bool_binop_eq_true
    (M : SmtModel) (hM : model_wf M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (evalOp : SmtValue -> SmtValue -> SmtValue)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hArgsOfNN :
      ∀ a b,
        __smtx_typeof (smtOp a b) ≠ SmtType.None ->
          __smtx_typeof a = SmtType.Bool ∧ __smtx_typeof b = SmtType.Bool)
    (hEval :
      ∀ a b,
        __smtx_model_eval M (smtOp a b) =
          evalOp (__smtx_model_eval M a) (__smtx_model_eval M b))
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_binary_uop_inv M eoOp x₁ x₂ rhs hSpine with
    ⟨y₁, y₂, hRhs, hArg₁, hArg₂⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂)
        (Term.Apply (Term.Apply (Term.UOp eoOp) y₁) y₂) hEqBool
    have hxOpNN :
        __smtx_typeof (smtOp (__eo_to_smt x₁) (__eo_to_smt x₂)) ≠
          SmtType.None := by
      rw [← hToSmt x₁ x₂]
      exact hTypes.2
    rcases hArgsOfNN (__eo_to_smt x₁) (__eo_to_smt x₂) hxOpNN with
      ⟨hx₁Bool, hx₂Bool⟩
    have hy₁Bool : __smtx_typeof (__eo_to_smt y₁) = SmtType.Bool := by
      rw [← smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁]
      exact hx₁Bool
    have hy₂Bool : __smtx_typeof (__eo_to_smt y₂) = SmtType.Bool := by
      rw [← smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂]
      exact hx₂Bool
    have hEval₁ :
        __smtx_model_eval M (__eo_to_smt x₁) =
          __smtx_model_eval M (__eo_to_smt y₁) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₁ y₁
        SmtType.Bool hx₁Bool hy₁Bool (by simp) (by simp) hArg₁
    have hEval₂ :
        __smtx_model_eval M (__eo_to_smt x₂) =
          __smtx_model_eval M (__eo_to_smt y₂) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₂ y₂
        SmtType.Bool hx₂Bool hy₂Bool (by simp) (by simp) hArg₂
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    rw [hToSmt x₁ x₂, hToSmt y₁ y₂]
    rw [hEval, hEval]
    rw [hEval₁, hEval₂]
    exact (RuleProofs.smt_value_rel_iff_model_eval_eq_true _ _).mp
      (RuleProofs.smt_value_rel_refl _)

theorem congTypeSpine_bool_binop_eq_has_bool_type
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hArgsOfNN :
      ∀ a b,
        __smtx_typeof (smtOp a b) ≠ SmtType.None ->
          __smtx_typeof a = SmtType.Bool ∧ __smtx_typeof b = SmtType.Bool)
    (hTypeBool :
      ∀ a b,
        __smtx_typeof a = SmtType.Bool ->
        __smtx_typeof b = SmtType.Bool ->
        __smtx_typeof (smtOp a b) = SmtType.Bool)
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_binary_uop_inv eoOp x₁ x₂ rhs hSpine with
    ⟨y₁, y₂, hRhs, hArg₁, hArg₂⟩
  subst hRhs
  have hxOpNN :
      __smtx_typeof (smtOp (__eo_to_smt x₁) (__eo_to_smt x₂)) ≠
        SmtType.None := by
    rw [← hToSmt x₁ x₂]
    exact hTrans
  rcases hArgsOfNN (__eo_to_smt x₁) (__eo_to_smt x₂) hxOpNN with
    ⟨hx₁Bool, hx₂Bool⟩
  have hy₁Bool : __smtx_typeof (__eo_to_smt y₁) = SmtType.Bool := by
    rw [← smt_type_eq_of_eq_bool_or_same x₁ y₁ hArg₁]
    exact hx₁Bool
  have hy₂Bool : __smtx_typeof (__eo_to_smt y₂) = SmtType.Bool := by
    rw [← smt_type_eq_of_eq_bool_or_same x₂ y₂ hArg₂]
    exact hx₂Bool
  have hxOpTy :
      __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂)) =
        SmtType.Bool := by
    rw [hToSmt]
    exact hTypeBool (__eo_to_smt x₁) (__eo_to_smt x₂) hx₁Bool hx₂Bool
  have hyOpTy :
      __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y₁) y₂)) =
        SmtType.Bool := by
    rw [hToSmt]
    exact hTypeBool (__eo_to_smt y₁) (__eo_to_smt y₂) hy₁Bool hy₂Bool
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂)
    (Term.Apply (Term.Apply (Term.UOp eoOp) y₁) y₂)
    (by rw [hxOpTy, hyOpTy])
    (by rw [hxOpTy]; simp)

theorem congTrueSpine_non_reg_unop_eq_true
    (M : SmtModel) (hM : model_wf M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm)
    (evalOp : SmtValue -> SmtValue)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply (Term.UOp eoOp) a) =
          smtOp (__eo_to_smt a))
    (hArgOfNN :
      ∀ a,
        __smtx_typeof (smtOp a) ≠ SmtType.None ->
          ∃ A,
            __smtx_typeof a = A ∧
              A ≠ SmtType.None ∧ A ≠ SmtType.RegLan)
    (hEval :
      ∀ a,
        __smtx_model_eval M (smtOp a) =
          evalOp (__smtx_model_eval M a))
    (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp eoOp) x) rhs ->
    eo_interprets M (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_unary_uop_inv M eoOp x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.UOp eoOp) x)
        (Term.Apply (Term.UOp eoOp) y) hEqBool
    have hxOpNN :
        __smtx_typeof (smtOp (__eo_to_smt x)) ≠ SmtType.None := by
      rw [← hToSmt x]
      exact hTypes.2
    rcases hArgOfNN (__eo_to_smt x) hxOpNN with
      ⟨A, hxA, hANN, hAReg⟩
    have hyA : __smtx_typeof (__eo_to_smt y) = A := by
      rw [← smt_type_eq_of_eq_true_or_same M x y hArg]
      exact hxA
    have hEvalArg :
        __smtx_model_eval M (__eo_to_smt x) =
          __smtx_model_eval M (__eo_to_smt y) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x y
        A hxA hyA hANN hAReg hArg
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    rw [hToSmt x, hToSmt y]
    rw [hEval, hEval]
    rw [hEvalArg]
    exact (RuleProofs.smt_value_rel_iff_model_eval_eq_true _ _).mp
      (RuleProofs.smt_value_rel_refl _)

theorem congTrueSpine_non_reg_unop_eq_true_of_eval_congr
    (M : SmtModel) (hM : model_wf M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply (Term.UOp eoOp) a) =
          smtOp (__eo_to_smt a))
    (hArgOfNN :
      ∀ a,
        __smtx_typeof (smtOp a) ≠ SmtType.None ->
          ∃ A,
            __smtx_typeof a = A ∧
              A ≠ SmtType.None ∧ A ≠ SmtType.RegLan)
    (hEvalCong :
      ∀ a b,
        __smtx_typeof a = __smtx_typeof b ->
          __smtx_model_eval M a = __smtx_model_eval M b ->
          __smtx_model_eval M (smtOp a) =
            __smtx_model_eval M (smtOp b))
    (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp eoOp) x) rhs ->
    eo_interprets M (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_unary_uop_inv M eoOp x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.UOp eoOp) x)
        (Term.Apply (Term.UOp eoOp) y) hEqBool
    have hxOpNN :
        __smtx_typeof (smtOp (__eo_to_smt x)) ≠ SmtType.None := by
      rw [← hToSmt x]
      exact hTypes.2
    rcases hArgOfNN (__eo_to_smt x) hxOpNN with
      ⟨A, hxA, hANN, hAReg⟩
    have hArgTy :
        __smtx_typeof (__eo_to_smt x) =
          __smtx_typeof (__eo_to_smt y) :=
      smt_type_eq_of_eq_true_or_same M x y hArg
    have hyA : __smtx_typeof (__eo_to_smt y) = A := by
      rw [← hArgTy]
      exact hxA
    have hEvalArg :
        __smtx_model_eval M (__eo_to_smt x) =
          __smtx_model_eval M (__eo_to_smt y) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x y
        A hxA hyA hANN hAReg hArg
    have hOpEval :
        __smtx_model_eval M (smtOp (__eo_to_smt x)) =
          __smtx_model_eval M (smtOp (__eo_to_smt y)) :=
      hEvalCong (__eo_to_smt x) (__eo_to_smt y) hArgTy hEvalArg
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    rw [hToSmt x, hToSmt y]
    rw [hOpEval]
    exact (RuleProofs.smt_value_rel_iff_model_eval_eq_true _ _).mp
      (RuleProofs.smt_value_rel_refl _)

theorem congTypeSpine_typecongr_unop_eq_has_bool_type
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply (Term.UOp eoOp) a) =
          smtOp (__eo_to_smt a))
    (hTypeCong :
      ∀ a b,
        __smtx_typeof a = __smtx_typeof b ->
          __smtx_typeof (smtOp a) = __smtx_typeof (smtOp b))
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp eoOp) x) ->
    CongTypeSpine (Term.Apply (Term.UOp eoOp) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_unary_uop_inv eoOp x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  have hArgTy :
      __smtx_typeof (__eo_to_smt x) =
        __smtx_typeof (__eo_to_smt y) :=
    smt_type_eq_of_eq_bool_or_same x y hArg
  have hOpTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp eoOp) x)) =
        __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp eoOp) y)) := by
    rw [hToSmt x, hToSmt y]
    exact hTypeCong (__eo_to_smt x) (__eo_to_smt y) hArgTy
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.UOp eoOp) x)
    (Term.Apply (Term.UOp eoOp) y)
    hOpTy
    hTrans

theorem congTypeSpine_purify_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp._at_purify) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp._at_purify) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp._at_purify) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type
    UserOp._at_purify SmtTerm._at_purify
    (by intro a; rfl)
    (by
      intro a b h
      simpa [__smtx_typeof] using h)
    x rhs

theorem congTrueSpine_purify_eq_true
    (M : SmtModel) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp._at_purify) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp._at_purify) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp UserOp._at_purify) x) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_unary_uop_inv M UserOp._at_purify x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · have hArgRel := smt_value_rel_of_eq_true_or_same M x y hArg
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm._at_purify (__eo_to_smt x)))
        (__smtx_model_eval M (SmtTerm._at_purify (__eo_to_smt y)))
    simpa [__smtx_model_eval, __smtx_model_eval__at_purify] using hArgRel

theorem congTypeSpine_typecongr_eotype_unop_eq_has_bool_type
    (eoOp : UserOp)
    (hTypeCong :
      ∀ a b,
        __smtx_typeof (__eo_to_smt a) = __smtx_typeof (__eo_to_smt b) ->
        __eo_typeof a = __eo_typeof b ->
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp eoOp) a)) =
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp eoOp) b)))
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp eoOp) x) ->
    CongTypeSpine (Term.Apply (Term.UOp eoOp) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_unary_uop_inv eoOp x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  have hArgTy :
      __smtx_typeof (__eo_to_smt x) =
        __smtx_typeof (__eo_to_smt y) :=
    smt_type_eq_of_eq_bool_or_same x y hArg
  have hArgEoTy : __eo_typeof x = __eo_typeof y :=
    eo_type_eq_of_eq_bool_or_same x y hArg
  have hOpTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp eoOp) x)) =
        __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp eoOp) y)) :=
    hTypeCong x y hArgTy hArgEoTy
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.UOp eoOp) x)
    (Term.Apply (Term.UOp eoOp) y)
    hOpTy
    hTrans

theorem congTrueSpine_eotype_non_reg_unop_eq_true_of_eval_congr
    (M : SmtModel) (hM : model_wf M)
    (eoOp : UserOp)
    (hArgOfNN :
      ∀ a,
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp eoOp) a)) ≠
          SmtType.None ->
          ∃ A,
            __smtx_typeof (__eo_to_smt a) = A ∧
              A ≠ SmtType.None ∧ A ≠ SmtType.RegLan)
    (hEvalCong :
      ∀ a b,
        __smtx_typeof (__eo_to_smt a) =
          __smtx_typeof (__eo_to_smt b) ->
        __eo_typeof a = __eo_typeof b ->
        __smtx_model_eval M (__eo_to_smt a) =
          __smtx_model_eval M (__eo_to_smt b) ->
        __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp eoOp) a)) =
          __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp eoOp) b)))
    (x rhs : Term) :
    RuleProofs.eo_has_bool_type (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp eoOp) x) rhs ->
    eo_interprets M (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_unary_uop_inv M eoOp x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.UOp eoOp) x)
        (Term.Apply (Term.UOp eoOp) y) hEqBool
    have hxOpNN :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp eoOp) x)) ≠
          SmtType.None :=
      hTypes.2
    rcases hArgOfNN x hxOpNN with ⟨A, hxA, hANN, hAReg⟩
    have hArgTy :
        __smtx_typeof (__eo_to_smt x) =
          __smtx_typeof (__eo_to_smt y) :=
      smt_type_eq_of_eq_true_or_same M x y hArg
    have hyA : __smtx_typeof (__eo_to_smt y) = A := by
      rw [← hArgTy]
      exact hxA
    have hArgEoTy : __eo_typeof x = __eo_typeof y :=
      eo_type_eq_of_eq_true_or_same M x y hArg
    have hEvalArg :
        __smtx_model_eval M (__eo_to_smt x) =
          __smtx_model_eval M (__eo_to_smt y) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x y
        A hxA hyA hANN hAReg hArg
    have hOpEval :
        __smtx_model_eval M
            (__eo_to_smt (Term.Apply (Term.UOp eoOp) x)) =
          __smtx_model_eval M
            (__eo_to_smt (Term.Apply (Term.UOp eoOp) y)) :=
      hEvalCong x y hArgTy hArgEoTy hEvalArg
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    rw [hOpEval]
    exact (RuleProofs.smt_value_rel_iff_model_eval_eq_true _ _).mp
      (RuleProofs.smt_value_rel_refl _)

theorem congTrueSpine_non_reg_indexed_unop_eq_true
    (M : SmtModel) (hM : model_wf M)
    (eoOp : UserOp1) (idx : Term)
    (smtOp : SmtTerm -> SmtTerm)
    (evalOp : SmtValue -> SmtValue)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply (Term.UOp1 eoOp idx) a) =
          smtOp (__eo_to_smt a))
    (hArgOfNN :
      ∀ a,
        __smtx_typeof (smtOp a) ≠ SmtType.None ->
          ∃ A,
            __smtx_typeof a = A ∧
              A ≠ SmtType.None ∧ A ≠ SmtType.RegLan)
    (hEval :
      ∀ a,
        __smtx_model_eval M (smtOp a) =
          evalOp (__smtx_model_eval M a))
    (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp1 eoOp idx) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp1 eoOp idx) x) rhs ->
    eo_interprets M (mkEq (Term.Apply (Term.UOp1 eoOp idx) x) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_indexed_unary_uop_inv M eoOp idx x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.UOp1 eoOp idx) x)
        (Term.Apply (Term.UOp1 eoOp idx) y) hEqBool
    have hxOpNN :
        __smtx_typeof (smtOp (__eo_to_smt x)) ≠ SmtType.None := by
      rw [← hToSmt x]
      exact hTypes.2
    rcases hArgOfNN (__eo_to_smt x) hxOpNN with
      ⟨A, hxA, hANN, hAReg⟩
    have hyA : __smtx_typeof (__eo_to_smt y) = A := by
      rw [← smt_type_eq_of_eq_true_or_same M x y hArg]
      exact hxA
    have hEvalArg :
        __smtx_model_eval M (__eo_to_smt x) =
          __smtx_model_eval M (__eo_to_smt y) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x y
        A hxA hyA hANN hAReg hArg
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    rw [hToSmt x, hToSmt y]
    rw [hEval, hEval]
    rw [hEvalArg]
    exact (RuleProofs.smt_value_rel_iff_model_eval_eq_true _ _).mp
      (RuleProofs.smt_value_rel_refl _)

theorem congTypeSpine_typecongr_indexed_unop_eq_has_bool_type
    (eoOp : UserOp1) (idx : Term) (smtOp : SmtTerm -> SmtTerm)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply (Term.UOp1 eoOp idx) a) =
          smtOp (__eo_to_smt a))
    (hTypeCong :
      ∀ a b,
        __smtx_typeof a = __smtx_typeof b ->
        __smtx_typeof (smtOp a) = __smtx_typeof (smtOp b))
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp1 eoOp idx) x) ->
    CongTypeSpine (Term.Apply (Term.UOp1 eoOp idx) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp1 eoOp idx) x) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_indexed_unary_uop_inv eoOp idx x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  have hArgTy :
      __smtx_typeof (__eo_to_smt x) =
        __smtx_typeof (__eo_to_smt y) :=
    smt_type_eq_of_eq_bool_or_same x y hArg
  have hOpTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp1 eoOp idx) x)) =
        __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp1 eoOp idx) y)) := by
    rw [hToSmt x, hToSmt y]
    exact hTypeCong (__eo_to_smt x) (__eo_to_smt y) hArgTy
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.UOp1 eoOp idx) x)
    (Term.Apply (Term.UOp1 eoOp idx) y)
    hOpTy
    hTrans

private theorem smtx_tuple_select_type_congr_local
    (T : SmtType) (idx x y : SmtTerm)
    (hTy : __smtx_typeof x = __smtx_typeof y) :
    __smtx_typeof (__eo_to_smt_tuple_select T idx x) =
      __smtx_typeof (__eo_to_smt_tuple_select T idx y) := by
  cases T <;> cases idx <;>
    try simp [__eo_to_smt_tuple_select]
  case Datatype.Numeral s dd n =>
    cases dd with
    | nil =>
        simp
    | cons s2 body rest =>
        cases rest with
        | nil =>
            by_cases hCond :
                (s = native_string_lit "@Tuple" ∧
                  s2 = native_string_lit "@Tuple") ∧
                    native_zleq 0 n = true
            · simp [hCond, __smtx_typeof, hTy]
            · simp [hCond]
        | cons s3 body3 rest3 =>
            simp

private theorem tuple_select_type_congr
    (idx x y : Term)
    (hSmt :
      __smtx_typeof (__eo_to_smt x) =
        __smtx_typeof (__eo_to_smt y))
    (hEo : __eo_typeof x = __eo_typeof y) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) x)) =
      __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) y)) := by
  change
    __smtx_typeof
        (__eo_to_smt_tuple_select
          (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt idx)
          (__eo_to_smt x)) =
      __smtx_typeof
        (__eo_to_smt_tuple_select
          (__smtx_typeof (__eo_to_smt y)) (__eo_to_smt idx)
          (__eo_to_smt y))
  rw [hSmt]
  exact smtx_tuple_select_type_congr_local
    (__smtx_typeof (__eo_to_smt y)) (__eo_to_smt idx)
    (__eo_to_smt x) (__eo_to_smt y) hSmt

theorem congTypeSpine_tuple_select_eq_has_bool_type
    (idx x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) x) ->
    CongTypeSpine
      (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) x) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_indexed_unary_uop_inv
      UserOp1.tuple_select idx x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  have hArgTy :
      __smtx_typeof (__eo_to_smt x) =
        __smtx_typeof (__eo_to_smt y) :=
    smt_type_eq_of_eq_bool_or_same x y hArg
  have hArgEoTy : __eo_typeof x = __eo_typeof y :=
    eo_type_eq_of_eq_bool_or_same x y hArg
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) x)
    (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) y)
    (tuple_select_type_congr idx x y hArgTy hArgEoTy)
    hTrans

private theorem tuple_select_arg_non_reg_of_non_none
    (idx x : Term) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) x)) ≠
      SmtType.None ->
      ∃ A,
        __smtx_typeof (__eo_to_smt x) = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  change
    __smtx_typeof
        (__eo_to_smt_tuple_select
          (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt idx)
          (__eo_to_smt x)) ≠ SmtType.None at hNN
  refine ⟨__smtx_typeof (__eo_to_smt x), rfl, ?_, ?_⟩
  · intro hNone
    apply hNN
    rw [hNone]
    simp [__eo_to_smt_tuple_select]
  · intro hReg
    apply hNN
    rw [hReg]
    simp [__eo_to_smt_tuple_select]

private theorem smtx_tuple_select_eval_congr_local
    (M : SmtModel) (T : SmtType) (idx x y : SmtTerm)
    (hEval : __smtx_model_eval M x = __smtx_model_eval M y) :
    __smtx_model_eval M (__eo_to_smt_tuple_select T idx x) =
      __smtx_model_eval M (__eo_to_smt_tuple_select T idx y) := by
  cases T <;> cases idx <;>
    try simp [__eo_to_smt_tuple_select]
  case Datatype.Numeral s dd n =>
    cases dd with
    | nil =>
        simp
    | cons s2 body rest =>
        cases rest with
        | nil =>
            by_cases hCond :
                (s = native_string_lit "@Tuple" ∧
                  s2 = native_string_lit "@Tuple") ∧
                    native_zleq 0 n = true
            · simp [hCond,
                __smtx_model_eval, hEval]
            · simp [hCond]
        | cons s3 body3 rest3 =>
            simp

private theorem tuple_select_eval_congr
    (M : SmtModel) (idx x y : Term)
    (hSmt :
      __smtx_typeof (__eo_to_smt x) =
        __smtx_typeof (__eo_to_smt y))
    (hEval :
      __smtx_model_eval M (__eo_to_smt x) =
        __smtx_model_eval M (__eo_to_smt y)) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) x)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) y)) := by
  change
    __smtx_model_eval M
        (__eo_to_smt_tuple_select
          (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt idx)
          (__eo_to_smt x)) =
      __smtx_model_eval M
        (__eo_to_smt_tuple_select
          (__smtx_typeof (__eo_to_smt y)) (__eo_to_smt idx)
          (__eo_to_smt y))
  rw [hSmt]
  exact smtx_tuple_select_eval_congr_local M
    (__smtx_typeof (__eo_to_smt y)) (__eo_to_smt idx)
    (__eo_to_smt x) (__eo_to_smt y) hEval

theorem congTrueSpine_tuple_select_eq_true
    (M : SmtModel) (hM : model_wf M)
    (idx x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) x) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) x) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_indexed_unary_uop_inv M
      UserOp1.tuple_select idx x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) x)
        (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) y)
        hEqBool
    have hxOpNN :
        __smtx_typeof
            (__eo_to_smt
              (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) x)) ≠
          SmtType.None :=
      hTypes.2
    rcases tuple_select_arg_non_reg_of_non_none idx x hxOpNN with
      ⟨A, hxA, hANN, hAReg⟩
    have hArgTy :
        __smtx_typeof (__eo_to_smt x) =
          __smtx_typeof (__eo_to_smt y) :=
      smt_type_eq_of_eq_true_or_same M x y hArg
    have hyA : __smtx_typeof (__eo_to_smt y) = A := by
      rw [← hArgTy]
      exact hxA
    have hArgEoTy : __eo_typeof x = __eo_typeof y :=
      eo_type_eq_of_eq_true_or_same M x y hArg
    have hEvalArg :
        __smtx_model_eval M (__eo_to_smt x) =
          __smtx_model_eval M (__eo_to_smt y) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x y
        A hxA hyA hANN hAReg hArg
    have hEvalOp :=
      tuple_select_eval_congr M idx x y hArgTy hEvalArg
    rw [hEvalOp]
    exact RuleProofs.smt_value_rel_refl _

theorem congTrueSpine_non_reg_indexed2_unop_eq_true
    (M : SmtModel) (hM : model_wf M)
    (eoOp : UserOp2) (idx₁ idx₂ : Term)
    (smtOp : SmtTerm -> SmtTerm)
    (evalOp : SmtValue -> SmtValue)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply (Term.UOp2 eoOp idx₁ idx₂) a) =
          smtOp (__eo_to_smt a))
    (hArgOfNN :
      ∀ a,
        __smtx_typeof (smtOp a) ≠ SmtType.None ->
          ∃ A,
            __smtx_typeof a = A ∧
              A ≠ SmtType.None ∧ A ≠ SmtType.RegLan)
    (hEval :
      ∀ a,
        __smtx_model_eval M (smtOp a) =
          evalOp (__smtx_model_eval M a))
    (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp2 eoOp idx₁ idx₂) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp2 eoOp idx₁ idx₂) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp2 eoOp idx₁ idx₂) x) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_indexed2_unary_uop_inv M eoOp idx₁ idx₂ x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.UOp2 eoOp idx₁ idx₂) x)
        (Term.Apply (Term.UOp2 eoOp idx₁ idx₂) y) hEqBool
    have hxOpNN :
        __smtx_typeof (smtOp (__eo_to_smt x)) ≠ SmtType.None := by
      rw [← hToSmt x]
      exact hTypes.2
    rcases hArgOfNN (__eo_to_smt x) hxOpNN with
      ⟨A, hxA, hANN, hAReg⟩
    have hyA : __smtx_typeof (__eo_to_smt y) = A := by
      rw [← smt_type_eq_of_eq_true_or_same M x y hArg]
      exact hxA
    have hEvalArg :
        __smtx_model_eval M (__eo_to_smt x) =
          __smtx_model_eval M (__eo_to_smt y) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x y
        A hxA hyA hANN hAReg hArg
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    rw [hToSmt x, hToSmt y]
    rw [hEval, hEval]
    rw [hEvalArg]
    exact (RuleProofs.smt_value_rel_iff_model_eval_eq_true _ _).mp
      (RuleProofs.smt_value_rel_refl _)

theorem congTypeSpine_typecongr_indexed2_unop_eq_has_bool_type
    (eoOp : UserOp2) (idx₁ idx₂ : Term)
    (smtOp : SmtTerm -> SmtTerm)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply (Term.UOp2 eoOp idx₁ idx₂) a) =
          smtOp (__eo_to_smt a))
    (hTypeCong :
      ∀ a b,
        __smtx_typeof a = __smtx_typeof b ->
        __smtx_typeof (smtOp a) = __smtx_typeof (smtOp b))
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp2 eoOp idx₁ idx₂) x) ->
    CongTypeSpine (Term.Apply (Term.UOp2 eoOp idx₁ idx₂) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp2 eoOp idx₁ idx₂) x) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_indexed2_unary_uop_inv eoOp idx₁ idx₂ x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  have hArgTy :
      __smtx_typeof (__eo_to_smt x) =
        __smtx_typeof (__eo_to_smt y) :=
    smt_type_eq_of_eq_bool_or_same x y hArg
  have hOpTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp2 eoOp idx₁ idx₂) x)) =
        __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp2 eoOp idx₁ idx₂) y)) := by
    rw [hToSmt x, hToSmt y]
    exact hTypeCong (__eo_to_smt x) (__eo_to_smt y) hArgTy
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.UOp2 eoOp idx₁ idx₂) x)
    (Term.Apply (Term.UOp2 eoOp idx₁ idx₂) y)
    hOpTy
    hTrans

theorem congTypeSpine_typecongr_indexed_binary_uop1_eq_has_bool_type
    (eoOp : UserOp1) (idx : Term)
    (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (hToSmt :
      ∀ a b,
        __eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp1 eoOp idx) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hTypeCong :
      ∀ a b a' b',
        __smtx_typeof a = __smtx_typeof a' ->
        __smtx_typeof b = __smtx_typeof b' ->
          __smtx_typeof (smtOp a b) = __smtx_typeof (smtOp a' b'))
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp1 eoOp idx) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp1 eoOp idx) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp1 eoOp idx) x₁) x₂) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_indexed_binary_uop1_inv eoOp idx x₁ x₂ rhs hSpine with
    ⟨y₁, y₂, hRhs, hArg₁, hArg₂⟩
  subst hRhs
  have hArgTy₁ :
      __smtx_typeof (__eo_to_smt x₁) =
        __smtx_typeof (__eo_to_smt y₁) :=
    smt_type_eq_of_eq_bool_or_same x₁ y₁ hArg₁
  have hArgTy₂ :
      __smtx_typeof (__eo_to_smt x₂) =
        __smtx_typeof (__eo_to_smt y₂) :=
    smt_type_eq_of_eq_bool_or_same x₂ y₂ hArg₂
  have hOpTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp1 eoOp idx) x₁) x₂)) =
        __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp1 eoOp idx) y₁) y₂)) := by
    rw [hToSmt x₁ x₂, hToSmt y₁ y₂]
    exact hTypeCong (__eo_to_smt x₁) (__eo_to_smt x₂)
      (__eo_to_smt y₁) (__eo_to_smt y₂) hArgTy₁ hArgTy₂
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply (Term.UOp1 eoOp idx) x₁) x₂)
    (Term.Apply (Term.Apply (Term.UOp1 eoOp idx) y₁) y₂)
    hOpTy
    hTrans

theorem congTrueSpine_non_reg_binop_eq_true
    (M : SmtModel) (hM : model_wf M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (evalOp : SmtValue -> SmtValue -> SmtValue)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hArgsOfNN :
      ∀ a b,
        __smtx_typeof (smtOp a b) ≠ SmtType.None ->
          ∃ A B,
            __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
              A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
              A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan)
    (hEval :
      ∀ a b,
        __smtx_model_eval M (smtOp a b) =
          evalOp (__smtx_model_eval M a) (__smtx_model_eval M b))
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_binary_uop_inv M eoOp x₁ x₂ rhs hSpine with
    ⟨y₁, y₂, hRhs, hArg₁, hArg₂⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂)
        (Term.Apply (Term.Apply (Term.UOp eoOp) y₁) y₂) hEqBool
    have hxOpNN :
        __smtx_typeof (smtOp (__eo_to_smt x₁) (__eo_to_smt x₂)) ≠
          SmtType.None := by
      rw [← hToSmt x₁ x₂]
      exact hTypes.2
    rcases hArgsOfNN (__eo_to_smt x₁) (__eo_to_smt x₂) hxOpNN with
      ⟨A, B, hx₁A, hx₂B, hANN, hBNN, hAReg, hBReg⟩
    have hy₁A : __smtx_typeof (__eo_to_smt y₁) = A := by
      rw [← smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁]
      exact hx₁A
    have hy₂B : __smtx_typeof (__eo_to_smt y₂) = B := by
      rw [← smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂]
      exact hx₂B
    have hEval₁ :
        __smtx_model_eval M (__eo_to_smt x₁) =
          __smtx_model_eval M (__eo_to_smt y₁) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₁ y₁
        A hx₁A hy₁A hANN hAReg hArg₁
    have hEval₂ :
        __smtx_model_eval M (__eo_to_smt x₂) =
          __smtx_model_eval M (__eo_to_smt y₂) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₂ y₂
        B hx₂B hy₂B hBNN hBReg hArg₂
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    rw [hToSmt x₁ x₂, hToSmt y₁ y₂]
    rw [hEval, hEval]
    rw [hEval₁, hEval₂]
    exact (RuleProofs.smt_value_rel_iff_model_eval_eq_true _ _).mp
      (RuleProofs.smt_value_rel_refl _)

theorem congTrueSpine_non_reg_binop_eq_true_of_eval_congr
    (M : SmtModel) (hM : model_wf M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hArgsOfNN :
      ∀ a b,
        __smtx_typeof (smtOp a b) ≠ SmtType.None ->
          ∃ A B,
            __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
              A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
              A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan)
    (hEvalCong :
      ∀ a b a' b',
        __smtx_typeof a = __smtx_typeof a' ->
        __smtx_typeof b = __smtx_typeof b' ->
        __smtx_model_eval M a = __smtx_model_eval M a' ->
        __smtx_model_eval M b = __smtx_model_eval M b' ->
          __smtx_model_eval M (smtOp a b) =
            __smtx_model_eval M (smtOp a' b'))
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_binary_uop_inv M eoOp x₁ x₂ rhs hSpine with
    ⟨y₁, y₂, hRhs, hArg₁, hArg₂⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂)
        (Term.Apply (Term.Apply (Term.UOp eoOp) y₁) y₂) hEqBool
    have hxOpNN :
        __smtx_typeof (smtOp (__eo_to_smt x₁) (__eo_to_smt x₂)) ≠
          SmtType.None := by
      rw [← hToSmt x₁ x₂]
      exact hTypes.2
    rcases hArgsOfNN (__eo_to_smt x₁) (__eo_to_smt x₂) hxOpNN with
      ⟨A, B, hx₁A, hx₂B, hANN, hBNN, hAReg, hBReg⟩
    have hArgTy₁ :
        __smtx_typeof (__eo_to_smt x₁) =
          __smtx_typeof (__eo_to_smt y₁) :=
      smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgTy₂ :
        __smtx_typeof (__eo_to_smt x₂) =
          __smtx_typeof (__eo_to_smt y₂) :=
      smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂
    have hy₁A : __smtx_typeof (__eo_to_smt y₁) = A := by
      rw [← hArgTy₁]
      exact hx₁A
    have hy₂B : __smtx_typeof (__eo_to_smt y₂) = B := by
      rw [← hArgTy₂]
      exact hx₂B
    have hEval₁ :
        __smtx_model_eval M (__eo_to_smt x₁) =
          __smtx_model_eval M (__eo_to_smt y₁) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₁ y₁
        A hx₁A hy₁A hANN hAReg hArg₁
    have hEval₂ :
        __smtx_model_eval M (__eo_to_smt x₂) =
          __smtx_model_eval M (__eo_to_smt y₂) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₂ y₂
        B hx₂B hy₂B hBNN hBReg hArg₂
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    rw [hToSmt x₁ x₂, hToSmt y₁ y₂]
    rw [hEvalCong (__eo_to_smt x₁) (__eo_to_smt x₂)
      (__eo_to_smt y₁) (__eo_to_smt y₂) hArgTy₁ hArgTy₂ hEval₁ hEval₂]
    exact (RuleProofs.smt_value_rel_iff_model_eval_eq_true _ _).mp
      (RuleProofs.smt_value_rel_refl _)

theorem congTypeSpine_typecongr_binop_eq_has_bool_type
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hTypeCong :
      ∀ a b a' b',
        __smtx_typeof a = __smtx_typeof a' ->
        __smtx_typeof b = __smtx_typeof b' ->
          __smtx_typeof (smtOp a b) = __smtx_typeof (smtOp a' b'))
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_binary_uop_inv eoOp x₁ x₂ rhs hSpine with
    ⟨y₁, y₂, hRhs, hArg₁, hArg₂⟩
  subst hRhs
  have hArgTy₁ :
      __smtx_typeof (__eo_to_smt x₁) =
        __smtx_typeof (__eo_to_smt y₁) :=
    smt_type_eq_of_eq_bool_or_same x₁ y₁ hArg₁
  have hArgTy₂ :
      __smtx_typeof (__eo_to_smt x₂) =
        __smtx_typeof (__eo_to_smt y₂) :=
    smt_type_eq_of_eq_bool_or_same x₂ y₂ hArg₂
  have hOpTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂)) =
        __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y₁) y₂)) := by
    rw [hToSmt x₁ x₂, hToSmt y₁ y₂]
    exact hTypeCong (__eo_to_smt x₁) (__eo_to_smt x₂)
      (__eo_to_smt y₁) (__eo_to_smt y₂) hArgTy₁ hArgTy₂
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂)
    (Term.Apply (Term.Apply (Term.UOp eoOp) y₁) y₂)
    hOpTy
    hTrans

theorem congTypeSpine_eq_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.eq SmtTerm.eq
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_eq_eq, typeof_eq_eq, ha, hb])
    x₁ x₂ rhs

theorem congTrueSpine_non_reg_ternop_eq_true
    (M : SmtModel) (hM : model_wf M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm)
    (evalOp : SmtValue -> SmtValue -> SmtValue -> SmtValue)
    (hToSmt :
      ∀ a b c,
        __eo_to_smt
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) c) =
          smtOp (__eo_to_smt a) (__eo_to_smt b) (__eo_to_smt c))
    (hArgsOfNN :
      ∀ a b c,
        __smtx_typeof (smtOp a b c) ≠ SmtType.None ->
          ∃ A B C,
            __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
              __smtx_typeof c = C ∧
              A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
              C ≠ SmtType.None ∧
              A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan ∧
              C ≠ SmtType.RegLan)
    (hEval :
      ∀ a b c,
        __smtx_model_eval M (smtOp a b c) =
          evalOp (__smtx_model_eval M a)
            (__smtx_model_eval M b) (__smtx_model_eval M c))
    (x₁ x₂ x₃ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) x₃)
        rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) x₃)
      rhs ->
    eo_interprets M
      (mkEq
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) x₃)
        rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_ternary_uop_inv M eoOp x₁ x₂ x₃ rhs hSpine with
    ⟨y₁, y₂, y₃, hRhs, hArg₁, hArg₂, hArg₃⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) x₃)
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) y₁) y₂) y₃)
        hEqBool
    have hxOpNN :
        __smtx_typeof
            (smtOp (__eo_to_smt x₁) (__eo_to_smt x₂) (__eo_to_smt x₃)) ≠
          SmtType.None := by
      rw [← hToSmt x₁ x₂ x₃]
      exact hTypes.2
    rcases hArgsOfNN (__eo_to_smt x₁) (__eo_to_smt x₂) (__eo_to_smt x₃)
        hxOpNN with
      ⟨A, B, C, hx₁A, hx₂B, hx₃C, hANN, hBNN, hCNN,
        hAReg, hBReg, hCReg⟩
    have hy₁A : __smtx_typeof (__eo_to_smt y₁) = A := by
      rw [← smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁]
      exact hx₁A
    have hy₂B : __smtx_typeof (__eo_to_smt y₂) = B := by
      rw [← smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂]
      exact hx₂B
    have hy₃C : __smtx_typeof (__eo_to_smt y₃) = C := by
      rw [← smt_type_eq_of_eq_true_or_same M x₃ y₃ hArg₃]
      exact hx₃C
    have hEval₁ :
        __smtx_model_eval M (__eo_to_smt x₁) =
          __smtx_model_eval M (__eo_to_smt y₁) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₁ y₁
        A hx₁A hy₁A hANN hAReg hArg₁
    have hEval₂ :
        __smtx_model_eval M (__eo_to_smt x₂) =
          __smtx_model_eval M (__eo_to_smt y₂) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₂ y₂
        B hx₂B hy₂B hBNN hBReg hArg₂
    have hEval₃ :
        __smtx_model_eval M (__eo_to_smt x₃) =
          __smtx_model_eval M (__eo_to_smt y₃) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₃ y₃
        C hx₃C hy₃C hCNN hCReg hArg₃
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    rw [hToSmt x₁ x₂ x₃, hToSmt y₁ y₂ y₃]
    rw [hEval, hEval]
    rw [hEval₁, hEval₂, hEval₃]
    exact (RuleProofs.smt_value_rel_iff_model_eval_eq_true _ _).mp
      (RuleProofs.smt_value_rel_refl _)

theorem congTypeSpine_typecongr_ternop_eq_has_bool_type
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm)
    (hToSmt :
      ∀ a b c,
        __eo_to_smt
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) c) =
          smtOp (__eo_to_smt a) (__eo_to_smt b) (__eo_to_smt c))
    (hTypeCong :
      ∀ a b c a' b' c',
        __smtx_typeof a = __smtx_typeof a' ->
        __smtx_typeof b = __smtx_typeof b' ->
        __smtx_typeof c = __smtx_typeof c' ->
          __smtx_typeof (smtOp a b c) =
            __smtx_typeof (smtOp a' b' c'))
    (x₁ x₂ x₃ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) x₃) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) x₃)
      rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) x₃)
        rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_ternary_uop_inv eoOp x₁ x₂ x₃ rhs hSpine with
    ⟨y₁, y₂, y₃, hRhs, hArg₁, hArg₂, hArg₃⟩
  subst hRhs
  have hArgTy₁ :
      __smtx_typeof (__eo_to_smt x₁) =
        __smtx_typeof (__eo_to_smt y₁) :=
    smt_type_eq_of_eq_bool_or_same x₁ y₁ hArg₁
  have hArgTy₂ :
      __smtx_typeof (__eo_to_smt x₂) =
        __smtx_typeof (__eo_to_smt y₂) :=
    smt_type_eq_of_eq_bool_or_same x₂ y₂ hArg₂
  have hArgTy₃ :
      __smtx_typeof (__eo_to_smt x₃) =
        __smtx_typeof (__eo_to_smt y₃) :=
    smt_type_eq_of_eq_bool_or_same x₃ y₃ hArg₃
  have hOpTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) x₃)) =
        __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) y₁) y₂) y₃)) := by
    rw [hToSmt x₁ x₂ x₃, hToSmt y₁ y₂ y₃]
    exact hTypeCong (__eo_to_smt x₁) (__eo_to_smt x₂) (__eo_to_smt x₃)
      (__eo_to_smt y₁) (__eo_to_smt y₂) (__eo_to_smt y₃)
      hArgTy₁ hArgTy₂ hArgTy₃
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) x₃)
    (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) y₁) y₂) y₃)
    hOpTy
    hTrans

theorem congTypeSpine_typecongr_quadop_eq_has_bool_type
    (eoOp : UserOp)
    (smtOp : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm)
    (hToSmt :
      ∀ a b c d,
        __eo_to_smt
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) c)
              d) =
          smtOp (__eo_to_smt a) (__eo_to_smt b) (__eo_to_smt c)
            (__eo_to_smt d))
    (hTypeCong :
      ∀ a b c d a' b' c' d',
        __smtx_typeof a = __smtx_typeof a' ->
        __smtx_typeof b = __smtx_typeof b' ->
        __smtx_typeof c = __smtx_typeof c' ->
        __smtx_typeof d = __smtx_typeof d' ->
          __smtx_typeof (smtOp a b c d) =
            __smtx_typeof (smtOp a' b' c' d'))
    (x₁ x₂ x₃ x₄ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) x₃)
        x₄) ->
    CongTypeSpine
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) x₃)
        x₄)
      rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) x₃)
          x₄)
        rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_quaternary_uop_inv eoOp x₁ x₂ x₃ x₄ rhs hSpine with
    ⟨y₁, y₂, y₃, y₄, hRhs, hArg₁, hArg₂, hArg₃, hArg₄⟩
  subst hRhs
  have hArgTy₁ :
      __smtx_typeof (__eo_to_smt x₁) =
        __smtx_typeof (__eo_to_smt y₁) :=
    smt_type_eq_of_eq_bool_or_same x₁ y₁ hArg₁
  have hArgTy₂ :
      __smtx_typeof (__eo_to_smt x₂) =
        __smtx_typeof (__eo_to_smt y₂) :=
    smt_type_eq_of_eq_bool_or_same x₂ y₂ hArg₂
  have hArgTy₃ :
      __smtx_typeof (__eo_to_smt x₃) =
        __smtx_typeof (__eo_to_smt y₃) :=
    smt_type_eq_of_eq_bool_or_same x₃ y₃ hArg₃
  have hArgTy₄ :
      __smtx_typeof (__eo_to_smt x₄) =
        __smtx_typeof (__eo_to_smt y₄) :=
    smt_type_eq_of_eq_bool_or_same x₄ y₄ hArg₄
  have hOpTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂)
                x₃)
              x₄)) =
        __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) y₁) y₂)
                y₃)
              y₄)) := by
    rw [hToSmt x₁ x₂ x₃ x₄, hToSmt y₁ y₂ y₃ y₄]
    exact hTypeCong (__eo_to_smt x₁) (__eo_to_smt x₂) (__eo_to_smt x₃)
      (__eo_to_smt x₄) (__eo_to_smt y₁) (__eo_to_smt y₂) (__eo_to_smt y₃)
      (__eo_to_smt y₄) hArgTy₁ hArgTy₂ hArgTy₃ hArgTy₄
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) x₃) x₄)
    (Term.Apply
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) y₁) y₂) y₃) y₄)
    hOpTy
    hTrans

theorem congTrueSpine_ite_eq_true
    (M : SmtModel) (hM : model_wf M)
    (c t e rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) e)
        rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) e)
      rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) e)
        rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_ternary_uop_inv M UserOp.ite c t e rhs hSpine with
    ⟨c', t', e', hRhs, hCond, hThen, hElse⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) e)
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c') t') e')
        hEqBool
    have hLeftNN :
        __smtx_typeof
            (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt t) (__eo_to_smt e)) ≠
          SmtType.None := by
      simpa using hTypes.2
    have hIteNN :
        term_has_non_none_type
          (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt t) (__eo_to_smt e)) := by
      unfold term_has_non_none_type
      exact hLeftNN
    rcases ite_args_of_non_none hIteNN with
      ⟨_T, hcBool, _htTy, _heTy, _hTNN⟩
    have hc'Bool :
        __smtx_typeof (__eo_to_smt c') = SmtType.Bool := by
      rw [← smt_type_eq_of_eq_true_or_same M c c' hCond]
      exact hcBool
    have hCondEval :
        __smtx_model_eval M (__eo_to_smt c) =
          __smtx_model_eval M (__eo_to_smt c') :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM c c'
        SmtType.Bool hcBool hc'Bool (by simp) (by simp) hCond
    have hc'NN : term_has_non_none_type (__eo_to_smt c') := by
      unfold term_has_non_none_type
      rw [hc'Bool]
      simp
    have hc'ValTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt c')) =
          SmtType.Bool := by
      simpa [hc'Bool] using
        smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt c') hc'NN
    rcases bool_value_canonical hc'ValTy with ⟨b, hc'Val⟩
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt t) (__eo_to_smt e)))
        (__smtx_model_eval M
          (SmtTerm.ite (__eo_to_smt c') (__eo_to_smt t') (__eo_to_smt e')))
    rw [smtx_model_eval_ite_term_eq, smtx_model_eval_ite_term_eq]
    rw [hCondEval, hc'Val]
    cases b with
    | false =>
        simpa [__smtx_model_eval_ite] using
          smt_value_rel_of_eq_true_or_same M e e' hElse
    | true =>
        simpa [__smtx_model_eval_ite] using
          smt_value_rel_of_eq_true_or_same M t t' hThen

theorem congTypeSpine_ite_eq_has_bool_type
    (c t e rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) e) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) e)
      rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) e)
        rhs) :=
  congTypeSpine_typecongr_ternop_eq_has_bool_type UserOp.ite SmtTerm.ite
    (by intro a b c; rfl)
    (by
      intro a b c a' b' c' ha hb hc
      rw [typeof_ite_eq, typeof_ite_eq, ha, hb, hc])
    c t e rhs

theorem smt_type_ne_none_of_apply_head
    {F A B : SmtType}
    (hHead :
      F = SmtType.FunType A B ∨ F = SmtType.DtcAppType A B) :
    F ≠ SmtType.None := by
  rcases hHead with hHead | hHead
  · rw [hHead]
    simp
  · rw [hHead]
    simp

theorem smt_type_ne_reglan_of_apply_head
    {F A B : SmtType}
    (hHead :
      F = SmtType.FunType A B ∨ F = SmtType.DtcAppType A B) :
    F ≠ SmtType.RegLan := by
  rcases hHead with hHead | hHead
  · rw [hHead]
    simp
  · rw [hHead]
    simp

theorem smt_value_rel_model_eval_apply_of_rel_core
    (M : SmtModel) (hM : model_wf M)
    (f g x y : SmtTerm)
    (hAppNN : __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None)
    (hFy : __smtx_typeof f = __smtx_typeof g)
    (hXy : __smtx_typeof x = __smtx_typeof y)
    (hFRel : RuleProofs.smt_value_rel (__smtx_model_eval M f) (__smtx_model_eval M g))
    (hXRel : RuleProofs.smt_value_rel (__smtx_model_eval M x) (__smtx_model_eval M y)) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval_apply M (__smtx_model_eval M f) (__smtx_model_eval M x))
      (__smtx_model_eval_apply M (__smtx_model_eval M g) (__smtx_model_eval M y)) := by
  rcases typeof_apply_non_none_cases hAppNN with
    ⟨A, B, hHead, hX, hA, _hB⟩
  have hFNN : term_has_non_none_type f := by
    unfold term_has_non_none_type
    exact smt_type_ne_none_of_apply_head hHead
  have hGNN : term_has_non_none_type g := by
    unfold term_has_non_none_type
    rw [← hFy]
    exact hFNN
  have hXNN : term_has_non_none_type x := by
    unfold term_has_non_none_type
    rw [hX]
    exact hA
  have hYNN : term_has_non_none_type y := by
    unfold term_has_non_none_type
    rw [← hXy]
    exact hXNN
  have hFPres :
      __smtx_typeof_value (__smtx_model_eval M f) = __smtx_typeof f :=
    smt_model_eval_preserves_type_of_non_none M hM f hFNN
  have hGPres :
      __smtx_typeof_value (__smtx_model_eval M g) = __smtx_typeof g :=
    smt_model_eval_preserves_type_of_non_none M hM g hGNN
  have hXPres :
      __smtx_typeof_value (__smtx_model_eval M x) = __smtx_typeof x :=
    smt_model_eval_preserves_type_of_non_none M hM x hXNN
  have hYPres :
      __smtx_typeof_value (__smtx_model_eval M y) = __smtx_typeof y :=
    smt_model_eval_preserves_type_of_non_none M hM y hYNN
  have hFNeReg : __smtx_typeof f ≠ SmtType.RegLan := by
    exact smt_type_ne_reglan_of_apply_head hHead
  have hANeReg : A ≠ SmtType.RegLan :=
    Smtm.smt_term_fun_like_arg_ne_reglan_of_non_none
      f hFNN hHead
  have hFEq : __smtx_model_eval M f = __smtx_model_eval M g :=
    RuleProofs.smt_value_rel_eq_of_type_ne_reglan
      hFPres (by simpa [hFy] using hGPres) hFNeReg hFRel
  have hXEq : __smtx_model_eval M x = __smtx_model_eval M y :=
    RuleProofs.smt_value_rel_eq_of_type_ne_reglan
      (by simpa [hX] using hXPres)
      (by
        rw [← hXy, hX] at hYPres
        exact hYPres)
      hANeReg hXRel
  rw [hFEq, hXEq]
  exact RuleProofs.smt_value_rel_refl _

theorem smt_apply_head_non_none_of_apply_non_none
    {f x : SmtTerm}
    (hAppNN :
      __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠
        SmtType.None) :
    __smtx_typeof f ≠ SmtType.None := by
  rcases typeof_apply_non_none_cases hAppNN with
    ⟨A, B, hHead, _hX, _hA, _hB⟩
  exact smt_type_ne_none_of_apply_head hHead

private theorem smt_term_ne_dt_sel_of_non_none_type
    {F : SmtTerm}
    (hF : __smtx_typeof F ≠ SmtType.None) :
    ∀ s d i j, F ≠ SmtTerm.DtSel s d i j := by
  intro s d i j h
  subst h
  exact hF (by simp)

private theorem smt_term_ne_dt_tester_of_non_none_type
    {F : SmtTerm}
    (hF : __smtx_typeof F ≠ SmtType.None) :
    ∀ s d i, F ≠ SmtTerm.DtTester s d i := by
  intro s d i h
  subst h
  exact hF (by simp)

theorem generic_apply_type_of_has_smt_translation
    (f x : Term)
    (hF : RuleProofs.eo_has_smt_translation f) :
    generic_apply_type (__eo_to_smt f) (__eo_to_smt x) :=
  generic_apply_type_of_non_datatype_head
    (smt_term_ne_dt_sel_of_non_none_type hF)
    (smt_term_ne_dt_tester_of_non_none_type hF)

theorem generic_apply_eval_of_has_smt_translation
    (f x : Term)
    (hF : RuleProofs.eo_has_smt_translation f) :
    generic_apply_eval (__eo_to_smt f) (__eo_to_smt x) :=
  generic_apply_eval_of_non_datatype_head
    (smt_term_ne_dt_sel_of_non_none_type hF)
    (smt_term_ne_dt_tester_of_non_none_type hF)

private theorem eo_typeof_apply_arg_stuck (F : Term) :
    __eo_typeof_apply F Term.Stuck = Term.Stuck := by
  cases F <;> rfl

private theorem eo_typeof_apply_dtc_eq_of_arg_ne_stuck
    (T U X : Term)
    (hX : X ≠ Term.Stuck) :
    __eo_typeof_apply (Term.DtcAppType T U) X =
      __eo_requires T X U := by
  cases X <;> simp [__eo_typeof_apply] at hX ⊢

private theorem eo_typeof_apply_fun_eq_of_arg_ne_stuck
    (T U X : Term)
    (hX : X ≠ Term.Stuck) :
    __eo_typeof_apply (Term.Apply (Term.Apply Term.FunType T) U) X =
      __eo_requires T X U := by
  cases X <;> simp [__eo_typeof_apply] at hX ⊢

private theorem smtx_typeof_apply_non_none_of_eo_typeof_apply_non_stuck
    (F X : Term)
    (hFValid : TranslationProofs.eo_type_valid F)
    (hApp : __eo_typeof_apply F X ≠ Term.Stuck) :
    __smtx_typeof_apply (__eo_to_smt_type F) (__eo_to_smt_type X) ≠
      SmtType.None := by
  cases F with
  | DtcAppType T U =>
      have hXNN : X ≠ Term.Stuck := by
        intro hX
        subst X
        exact hApp (eo_typeof_apply_arg_stuck _)
      rw [eo_typeof_apply_dtc_eq_of_arg_ne_stuck T U X hXNN] at hApp
      have hAppReq : __eo_requires T X U ≠ Term.Stuck := hApp
      have hX : T = X := eo_requires_arg_eq_of_ne_stuck hAppReq
      subst X
      have hTransNN :
          __eo_to_smt_type (Term.DtcAppType T U) ≠ SmtType.None :=
        TranslationProofs.eo_type_valid_non_none hFValid
      have hTNN : __eo_to_smt_type T ≠ SmtType.None := by
        intro hT
        apply hTransNN
        simp [__eo_to_smt_type, hT, __smtx_typeof_guard]
      have hUNN : __eo_to_smt_type U ≠ SmtType.None := by
        intro hU
        apply hTransNN
        simp [__eo_to_smt_type, hU, __smtx_typeof_guard]
      simp [__eo_to_smt_type, __smtx_typeof_apply, __smtx_typeof_guard,
        native_ite, native_Teq, hTNN, hUNN]
  | Apply f U =>
      cases f with
      | Apply f' T =>
          cases f' with
          | FunType =>
              have hXNN : X ≠ Term.Stuck := by
                intro hX
                subst X
                exact hApp (eo_typeof_apply_arg_stuck _)
              rw [eo_typeof_apply_fun_eq_of_arg_ne_stuck T U X hXNN] at hApp
              have hAppReq : __eo_requires T X U ≠ Term.Stuck := hApp
              have hX : T = X := eo_requires_arg_eq_of_ne_stuck hAppReq
              subst X
              have hTransNN :
                  __eo_to_smt_type
                      (Term.Apply (Term.Apply Term.FunType T) U) ≠
                    SmtType.None :=
                TranslationProofs.eo_type_valid_non_none hFValid
              have hTNN : __eo_to_smt_type T ≠ SmtType.None := by
                intro hT
                apply hTransNN
                simp [TranslationProofs.eo_to_smt_type_fun, hT,
                  __smtx_typeof_guard]
              have hUNN : __eo_to_smt_type U ≠ SmtType.None := by
                intro hU
                apply hTransNN
                simp [TranslationProofs.eo_to_smt_type_fun, hU,
                  __smtx_typeof_guard]
              simp [TranslationProofs.eo_to_smt_type_fun,
                __smtx_typeof_apply, __smtx_typeof_guard, native_ite,
                native_Teq, hTNN, hUNN]
          | _ =>
              exact False.elim (hApp (by cases X <;> simp [__eo_typeof_apply]))
      | _ =>
          exact False.elim (hApp (by cases X <;> simp [__eo_typeof_apply]))
  | _ =>
      exact False.elim (hApp (by cases X <;> simp [__eo_typeof_apply]))

theorem smt_apply_type_none_of_arg_none
    (f x : SmtTerm) :
    __smtx_typeof x = SmtType.None ->
    __smtx_typeof (SmtTerm.Apply f x) = SmtType.None := by
  intro hx
  by_cases hNN : __smtx_typeof (SmtTerm.Apply f x) = SmtType.None
  · exact hNN
  · exfalso
    by_cases hSelWitness : ∃ s d i j, f = SmtTerm.DtSel s d i j
    · rcases hSelWitness with ⟨s, d, i, j, rfl⟩
      have hArg : __smtx_typeof x = SmtType.Datatype s d :=
        dt_sel_arg_datatype_of_non_none (s := s) (d := d) (i := i)
          (j := j) (x := x) hNN
      rw [hx] at hArg
      cases hArg
    · by_cases hTesterWitness : ∃ s d i, f = SmtTerm.DtTester s d i
      · rcases hTesterWitness with ⟨s, d, i, rfl⟩
        have hArg : __smtx_typeof x = SmtType.Datatype s d :=
          dt_tester_arg_datatype_of_non_none (s := s) (d := d) (i := i)
            (x := x) hNN
        rw [hx] at hArg
        cases hArg
      · have hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j := by
          intro s d i j hEq
          exact hSelWitness ⟨s, d, i, j, hEq⟩
        have hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i := by
          intro s d i hEq
          exact hTesterWitness ⟨s, d, i, hEq⟩
        have hGeneric : generic_apply_type f x :=
          generic_apply_type_of_non_datatype_head hSel hTester
        have hApply :
            __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠
              SmtType.None := by
          unfold generic_apply_type at hGeneric
          rw [← hGeneric]
          exact hNN
        rcases typeof_apply_non_none_cases hApply with
          ⟨A, _B, _hHead, hArg, hA, _hB⟩
        rw [hx] at hArg
        exact hA hArg.symm

theorem eo_apply_apply_generic_type_none_of_arg_none
    (f z x : Term)
    (hToSmt :
      __eo_to_smt (Term.Apply (Term.Apply f z) x) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply f z)) (__eo_to_smt x)) :
    __smtx_typeof (__eo_to_smt x) = SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply f z) x)) =
      SmtType.None := by
  intro hx
  rw [hToSmt]
  exact smt_apply_type_none_of_arg_none
    (__eo_to_smt (Term.Apply f z)) (__eo_to_smt x) hx

theorem smt_binop_type_none_of_second_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm) (a b : SmtTerm)
    (hArgs :
      ∀ a b,
        __smtx_typeof (op a b) ≠ SmtType.None ->
          ∃ A B,
            __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
              A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
              A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof (op a b) = SmtType.None := by
  intro hb
  by_cases hNone : __smtx_typeof (op a b) = SmtType.None
  · exact hNone
  · exfalso
    rcases hArgs a b hNone with
      ⟨_A, B, _ha, hbTy, _hANN, hBNN, _hAReg, _hBReg⟩
    rw [hb] at hbTy
    exact hBNN hbTy.symm

theorem smt_bool_binop_type_none_of_second_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm) (a b : SmtTerm)
    (hArg :
      __smtx_typeof (op a b) ≠ SmtType.None ->
        __smtx_typeof b = SmtType.Bool) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof (op a b) = SmtType.None := by
  intro hb
  by_cases hNone : __smtx_typeof (op a b) = SmtType.None
  · exact hNone
  · exfalso
    have hbBool := hArg hNone
    rw [hb] at hbBool
    cases hbBool

theorem smt_reglan_binop_type_none_of_second_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          native_ite (native_Teq (__smtx_typeof a) SmtType.RegLan)
            (native_ite (native_Teq (__smtx_typeof b) SmtType.RegLan)
              SmtType.RegLan SmtType.None)
            SmtType.None)
    (a b : SmtTerm) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof (op a b) = SmtType.None := by
  intro hb
  by_cases hNone : __smtx_typeof (op a b) = SmtType.None
  · exact hNone
  · exfalso
    have hTerm : term_has_non_none_type (op a b) := by
      unfold term_has_non_none_type
      exact hNone
    have hArgs := reglan_binop_args_of_non_none (op := op) (hTy a b) hTerm
    rw [hb] at hArgs
    cases hArgs.2

theorem smt_seq_char_reglan_binop_type_none_of_second_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          native_ite (native_Teq (__smtx_typeof a) (SmtType.Seq SmtType.Char))
            (native_ite (native_Teq (__smtx_typeof b) SmtType.RegLan)
              SmtType.Bool SmtType.None)
            SmtType.None)
    (a b : SmtTerm) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof (op a b) = SmtType.None := by
  intro hb
  by_cases hNone : __smtx_typeof (op a b) = SmtType.None
  · exact hNone
  · exfalso
    have hTerm : term_has_non_none_type (op a b) := by
      unfold term_has_non_none_type
      exact hNone
    have hArgs := seq_char_reglan_args_of_non_none
      (op := op) (hTy a b) hTerm
    rw [hb] at hArgs
    cases hArgs.2

theorem smt_eq_type_none_of_second_arg_none
    (a b : SmtTerm) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof (SmtTerm.eq a b) = SmtType.None := by
  intro hb
  by_cases hNone : __smtx_typeof (SmtTerm.eq a b) = SmtType.None
  · exact hNone
  · exfalso
    have hEqNN :
        __smtx_typeof_eq (__smtx_typeof a) (__smtx_typeof b) ≠
          SmtType.None := by
      simpa [typeof_eq_eq] using hNone
    have hInfo := cong_smtx_typeof_eq_non_none hEqNN
    rw [hb] at hInfo
    exact hInfo.2 hInfo.1

theorem smt_ite_type_none_of_else_arg_none
    (c t e : SmtTerm) :
    __smtx_typeof e = SmtType.None ->
    __smtx_typeof (SmtTerm.ite c t e) = SmtType.None := by
  intro he
  by_cases hNone : __smtx_typeof (SmtTerm.ite c t e) = SmtType.None
  · exact hNone
  · exfalso
    have hTerm : term_has_non_none_type (SmtTerm.ite c t e) := by
      unfold term_has_non_none_type
      exact hNone
    rcases ite_args_of_non_none hTerm with ⟨T, _hc, _ht, heT, hTNN⟩
    rw [he] at heT
    exact hTNN heT.symm

theorem smt_ternop_type_none_of_third_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm)
    (a b c : SmtTerm)
    (hArgs :
      ∀ a b c,
        __smtx_typeof (op a b c) ≠ SmtType.None ->
          ∃ A B C,
            __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
              __smtx_typeof c = C ∧
              A ≠ SmtType.None ∧ B ≠ SmtType.None ∧ C ≠ SmtType.None ∧
              A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan ∧
              C ≠ SmtType.RegLan) :
    __smtx_typeof c = SmtType.None ->
    __smtx_typeof (op a b c) = SmtType.None := by
  intro hc
  by_cases hNone : __smtx_typeof (op a b c) = SmtType.None
  · exact hNone
  · exfalso
    rcases hArgs a b c hNone with
      ⟨_A, _B, C, _ha, _hb, hcTy, _hANN, _hBNN, hCNN,
        _hAReg, _hBReg, _hCReg⟩
    rw [hc] at hcTy
    exact hCNN hcTy.symm

theorem smt_str_replace_re_type_none_of_third_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm)
    (hTy :
      ∀ a b c,
        __smtx_typeof (op a b c) =
          native_ite
            (native_Teq (__smtx_typeof a) (SmtType.Seq SmtType.Char))
            (native_ite (native_Teq (__smtx_typeof b) SmtType.RegLan)
              (native_ite
                (native_Teq (__smtx_typeof c) (SmtType.Seq SmtType.Char))
                (SmtType.Seq SmtType.Char) SmtType.None)
              SmtType.None)
            SmtType.None)
    (a b c : SmtTerm) :
    __smtx_typeof c = SmtType.None ->
    __smtx_typeof (op a b c) = SmtType.None := by
  intro hc
  by_cases hNone : __smtx_typeof (op a b c) = SmtType.None
  · exact hNone
  · exfalso
    have hTerm : term_has_non_none_type (op a b c) := by
      unfold term_has_non_none_type
      exact hNone
    have hArgs := str_replace_re_args_of_non_none (op := op) (hTy a b c) hTerm
    rw [hc] at hArgs
    cases hArgs.2.2

theorem smt_str_indexof_re_type_none_of_third_arg_none
    (a b c : SmtTerm) :
    __smtx_typeof c = SmtType.None ->
    __smtx_typeof (SmtTerm.str_indexof_re a b c) = SmtType.None := by
  intro hc
  by_cases hNone :
      __smtx_typeof (SmtTerm.str_indexof_re a b c) = SmtType.None
  · exact hNone
  · exfalso
    have hTerm :
        term_has_non_none_type (SmtTerm.str_indexof_re a b c) := by
      unfold term_has_non_none_type
      exact hNone
    have hArgs := str_indexof_re_args_of_non_none hTerm
    rw [hc] at hArgs
    cases hArgs.2.2

theorem smt_str_indexof_re_split_type_none_of_third_arg_none
    (a b c : SmtTerm) :
    __smtx_typeof c = SmtType.None ->
    __smtx_typeof (SmtTerm.str_indexof_re_split a b c) = SmtType.None := by
  intro hc
  by_cases hNone :
      __smtx_typeof (SmtTerm.str_indexof_re_split a b c) = SmtType.None
  · exact hNone
  · exfalso
    have hTerm :
        term_has_non_none_type (SmtTerm.str_indexof_re_split a b c) := by
      unfold term_has_non_none_type
      exact hNone
    have hArgs := str_indexof_re_split_args_of_non_none hTerm
    rw [hc] at hArgs
    cases hArgs.2.2

theorem eo_to_smt_set_insert_type_none_of_arg_none :
    ∀ xs a,
      __smtx_typeof a = SmtType.None ->
      __smtx_typeof (__eo_to_smt_set_insert xs a) = SmtType.None := by
  intro xs a ha
  cases xs <;> try simp [__eo_to_smt_set_insert]
  case Apply f tail =>
    cases f <;> try simp [__eo_to_smt_set_insert]
    case UOp op =>
      cases op <;> simp [__eo_to_smt_set_insert, ha, native_ite, native_Teq]
    case Apply f' head =>
      cases f' <;> try simp [__eo_to_smt_set_insert]
      case UOp op =>
        cases op <;> try simp [__eo_to_smt_set_insert]
        have hTail :
            __smtx_typeof (__eo_to_smt_set_insert tail a) =
              SmtType.None :=
          eo_to_smt_set_insert_type_none_of_arg_none tail a ha
        change
          __smtx_typeof
              (SmtTerm.set_union (SmtTerm.set_singleton (__eo_to_smt head))
                (__eo_to_smt_set_insert tail a)) = SmtType.None
        rw [typeof_set_union_eq, hTail]
        cases __smtx_typeof (SmtTerm.set_singleton (__eo_to_smt head)) <;>
          simp [__smtx_typeof_sets_op_2]
termination_by xs a _ => xs

theorem eo_to_smt_exists_type_none_of_body_none :
    ∀ xs body,
      __smtx_typeof body = SmtType.None ->
      __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.None := by
  intro xs body hBody
  cases xs <;> try simp [__eo_to_smt_exists]
  case __eo_List_nil =>
    exact hBody
  case Apply f tail =>
    cases f <;> try simp [__eo_to_smt_exists]
    case Apply f' head =>
      cases f' <;> try simp [__eo_to_smt_exists]
      case __eo_List_cons =>
        cases head <;> try simp [__eo_to_smt_exists]
        case Var name T =>
          cases name <;> try simp [__eo_to_smt_exists]
          case String s =>
            have hTail : __smtx_typeof (__eo_to_smt_exists tail body) =
                SmtType.None :=
              eo_to_smt_exists_type_none_of_body_none tail body hBody
            change
              __smtx_typeof
                  (SmtTerm.exists s (__eo_to_smt_type T)
                    (__eo_to_smt_exists tail body)) = SmtType.None
            rw [smtx_typeof_exists_term_eq, hTail]
            rfl
termination_by xs body _ => xs

theorem eo_to_smt_forall_type_none_of_body_none
    (xs body : Term) :
    __smtx_typeof (__eo_to_smt body) = SmtType.None ->
    __smtx_typeof
        (SmtTerm.not (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt body)))) =
      SmtType.None := by
  intro hBody
  have hNotBody :
      __smtx_typeof (SmtTerm.not (__eo_to_smt body)) = SmtType.None := by
    rw [typeof_not_eq, hBody]
    rfl
  have hExists :
      __smtx_typeof (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt body))) =
        SmtType.None :=
    eo_to_smt_exists_type_none_of_body_none xs
      (SmtTerm.not (__eo_to_smt body)) hNotBody
  rw [typeof_not_eq, hExists]
  rfl

theorem eo_to_smt_apply_generic_of_has_smt_translation
    (f x : Term)
    (hTransF : RuleProofs.eo_has_smt_translation f) :
    __eo_to_smt (Term.Apply f x) =
      SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x) := by
  unfold RuleProofs.eo_has_smt_translation at hTransF
  cases f <;> try rfl
  case UOp op =>
    cases op <;> try rfl
    all_goals
      exfalso
      apply hTransF
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none
  case UOp1 op i =>
    cases op <;> try rfl
    all_goals
      exfalso
      apply hTransF
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none
  case UOp2 op i j =>
    cases op <;> try rfl
    all_goals
      exfalso
      apply hTransF
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none
  case Apply f a =>
    cases f <;> try rfl
    case UOp op =>
      cases op <;> try rfl
      all_goals
        exfalso
        apply hTransF
        change __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt a)) =
          SmtType.None
        simp [__smtx_typeof, __smtx_typeof_apply]
    case UOp1 op i =>
      cases op <;> try rfl
      all_goals
        exfalso
        apply hTransF
        change __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt a)) =
          SmtType.None
        simp [__smtx_typeof, __smtx_typeof_apply]
    case Apply f' b =>
      cases f' <;> try rfl
      case UOp op =>
        cases op <;> try rfl
        all_goals
          exfalso
          apply hTransF
          change
            __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt b))
                (__eo_to_smt a)) = SmtType.None
          simp [__smtx_typeof, __smtx_typeof_apply]
      case Apply f'' c =>
        cases f'' <;> try rfl
        case UOp op =>
          cases op <;> try rfl
          all_goals
            exfalso
            apply hTransF
            change
              __smtx_typeof
                (SmtTerm.Apply
                  (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt c))
                    (__eo_to_smt b))
                  (__eo_to_smt a)) = SmtType.None
            simp [__smtx_typeof, __smtx_typeof_apply]

theorem eo_typeof_apply_eq_of_has_smt_translation
    (f x : Term)
    (hTransF : RuleProofs.eo_has_smt_translation f) :
    __eo_typeof (Term.Apply f x) =
      __eo_typeof_apply (__eo_typeof f) (__eo_typeof x) := by
  exact TranslationProofs.eo_typeof_apply_eq_of_non_none_translation
    f x hTransF

theorem eo_has_smt_translation_apply_of_head_arg_translation_and_type
    (f x : Term)
    (hF : RuleProofs.eo_has_smt_translation f)
    (hX : RuleProofs.eo_has_smt_translation x)
    (hTy : __eo_typeof (Term.Apply f x) ≠ Term.Stuck) :
    RuleProofs.eo_has_smt_translation (Term.Apply f x) := by
  unfold RuleProofs.eo_has_smt_translation
  rw [eo_to_smt_apply_generic_of_has_smt_translation f x hF]
  have hGeneric : generic_apply_type (__eo_to_smt f) (__eo_to_smt x) :=
    generic_apply_type_of_has_smt_translation f x hF
  unfold generic_apply_type at hGeneric
  rw [hGeneric]
  have hFMatch :
      __smtx_typeof (__eo_to_smt f) = __eo_to_smt_type (__eo_typeof f) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation f hF
  have hXMatch :
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hX
  rw [hFMatch, hXMatch]
  have hEoApply :
      __eo_typeof_apply (__eo_typeof f) (__eo_typeof x) ≠ Term.Stuck := by
    have hEq := eo_typeof_apply_eq_of_has_smt_translation f x hF
    rwa [← hEq]
  have hFValid :
      TranslationProofs.eo_type_valid (__eo_typeof f) :=
    TranslationProofs.eo_type_valid_typeof_of_smt_translation f hF
  exact smtx_typeof_apply_non_none_of_eo_typeof_apply_non_stuck
    (__eo_typeof f) (__eo_typeof x) hFValid hEoApply

theorem eq_typeof_bool_left_ne_stuck (x y : Term) :
    __eo_typeof (mkEq x y) = Term.Bool ->
    __eo_typeof x ≠ Term.Stuck := by
  intro h
  change __eo_typeof_eq (__eo_typeof x) (__eo_typeof y) = Term.Bool at h
  cases hx : __eo_typeof x <;>
    cases hy : __eo_typeof y <;>
      simp [__eo_typeof_eq, hx, hy] at h ⊢

end CongSupport
