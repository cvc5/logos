module

public import Cpc.SmtEval
import all Cpc.SmtEval
public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport
public import Cpc.Proofs.RuleSupport.StrEqReplSupport
import all Cpc.Proofs.RuleSupport.StrEqReplSupport
public import Cpc.Proofs.RuleSupport.StrOverlapSupport
import all Cpc.Proofs.RuleSupport.StrOverlapSupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

/-!
Greedy-scan occurrence theory for `native_seq_replace_all`.

`str.replace_all` (and the `@strings_num_occur` / `@strings_occur_index` /
`@strings_replace_all_result` skolems of the `string_reduction` rule) are all
governed by the same leftmost greedy scan: repeatedly find the first
occurrence of the pattern and jump past it.  This file develops that scan as
the list `occEnds pat xs` of *end positions* of the replaced occurrences and
proves the facts consumed by the `str_replace_all` case of
`string_reduction`:

* `native_seq_replace_all` length arithmetic (`replace_all_length_int`),
  which gives the `@strings_num_occur` skolem its meaning;
* the prefix-count characterisation (`occEnds_take`), which shows the
  `@strings_occur_index` choice body has the scan boundaries as its unique
  witnesses (`occ_count_unique`);
* the scan-step decompositions used by the quantified recurrence of the
  reduction predicate (`replace_all_drop_bound_step`, `indexof_at_bound`,
  ...).
-/

namespace StrReplaceAllSupport

/-! Inlined from `StringRewriteSupport` (not imported here to keep this file
off the heavier congruence-support dependency chain). -/

theorem native_seq_prefix_eq_append_self
    (pat suffix : List SmtValue) :
    native_seq_prefix_eq pat (pat ++ suffix) = true := by
  exact native_seq_prefix_eq_append_of_eq_true pat pat suffix
    (native_seq_prefix_eq_self pat)

theorem native_seq_indexof_rec_le_of_prefix_at
    (pat : List SmtValue) :
    ∀ (xs : List SmtValue) (i fuel offset : Nat),
      offset < fuel →
      native_seq_prefix_eq pat (xs.drop offset) = true →
      ∃ found : Nat,
        found ≤ offset ∧
          native_seq_indexof_rec xs pat i fuel = Int.ofNat (i + found) := by
  intro xs i fuel
  induction fuel generalizing xs i with
  | zero =>
      intro offset hOffset
      omega
  | succ fuel ih =>
      intro offset hOffset hPrefix
      unfold native_seq_indexof_rec
      by_cases hHere : native_seq_prefix_eq pat xs = true
      · rw [if_pos hHere]
        exact ⟨0, Nat.zero_le _, by simp⟩
      · rw [if_neg hHere]
        cases offset with
        | zero =>
            simp at hPrefix
            exact False.elim (hHere hPrefix)
        | succ offset =>
            cases xs with
            | nil =>
                have hNil : native_seq_prefix_eq pat [] = true := by
                  simpa using hPrefix
                exact False.elim (hHere hNil)
            | cons x xs =>
                have hTailPrefix :
                    native_seq_prefix_eq pat (xs.drop offset) = true := by
                  simpa using hPrefix
                rcases ih xs (i + 1) offset (by omega) hTailPrefix with
                  ⟨found, hFoundLe, hRec⟩
                refine ⟨found + 1, by omega, ?_⟩
                change native_seq_indexof_rec xs pat (i + 1) fuel =
                  Int.ofNat (i + (found + 1))
                rw [hRec]
                congr 1
                omega

theorem native_seq_indexof_zero_le_of_prefix_at
    (xs pat : List SmtValue) (offset : Nat)
    (hFit : offset + pat.length ≤ xs.length)
    (hPrefix : native_seq_prefix_eq pat (xs.drop offset) = true) :
    0 ≤ native_seq_indexof xs pat 0 ∧
      native_seq_indexof xs pat 0 ≤ Int.ofNat offset := by
  have hPatFit : pat.length ≤ xs.length := by omega
  have hOffsetFuel : offset < xs.length - pat.length + 1 := by omega
  rcases native_seq_indexof_rec_le_of_prefix_at pat xs 0
      (xs.length - pat.length + 1) offset hOffsetFuel hPrefix with
    ⟨found, hFoundLe, hRec⟩
  rw [native_seq_indexof_eq_rec]
  simp only [Int.reduceLT, ↓reduceIte, Int.toNat_zero, Nat.zero_add]
  simp only [List.drop_zero]
  rw [dif_pos hPatFit, hRec]
  constructor
  · exact Int.natCast_nonneg _
  · apply Int.ofNat_le.mpr
    simpa using hFoundLe

theorem native_seq_prefix_eq_at_index_of_nonneg
    (xs pat : List SmtValue)
    (hNonneg : 0 ≤ native_seq_indexof xs pat 0) :
    native_seq_prefix_eq pat
        (xs.drop (Int.toNat (native_seq_indexof xs pat 0))) = true := by
  let k := Int.toNat (native_seq_indexof xs pat 0)
  have hBound := StrEqReplSupport.native_seq_indexof_zero_bounds_of_nonneg
    xs pat hNonneg
  have hKLe : k ≤ xs.length := by omega
  have hDecomp := StrEqReplSupport.native_seq_indexof_zero_decomp_take_drop
    xs pat hNonneg
  have hDropped := congrArg (List.drop k) hDecomp
  have hTakeLen : (xs.take k).length = k := by
    simp [List.length_take, Nat.min_eq_left hKLe]
  have hDropEq :
      pat ++ xs.drop (k + pat.length) = xs.drop k := by
    simpa [k, hTakeLen] using hDropped
  rw [← hDropEq]
  exact native_seq_prefix_eq_append_self pat _

/-- End positions of the greedy leftmost occurrences of `pat` in `xs`. -/
@[expose] def occEndsAux (fuel : Nat) (pat : List SmtValue) :
    List SmtValue -> List Nat
  | xs =>
      match fuel with
      | 0 => []
      | fuel + 1 =>
          match pat with
          | [] => []
          | _ =>
              let idx := native_seq_indexof xs pat 0
              if idx < 0 then
                []
              else
                let n := Int.toNat idx
                (n + pat.length) ::
                  (occEndsAux fuel pat (xs.drop (n + pat.length))).map
                    (· + (n + pat.length))

/-- End positions of the greedy leftmost occurrences of `pat` in `xs`. -/
@[expose] def occEnds (pat xs : List SmtValue) : List Nat :=
  occEndsAux (xs.length + 1) pat xs

theorem occEndsAux_nil_pat (fuel : Nat) (xs : List SmtValue) :
    occEndsAux fuel [] xs = [] := by
  cases fuel <;> simp [occEndsAux]

theorem occEnds_nil_pat (xs : List SmtValue) : occEnds [] xs = [] :=
  occEndsAux_nil_pat _ xs

theorem occEndsAux_succ (fuel : Nat) (p : SmtValue) (ps xs : List SmtValue) :
    occEndsAux (fuel + 1) (p :: ps) xs =
      if native_seq_indexof xs (p :: ps) 0 < 0 then
        []
      else
        (Int.toNat (native_seq_indexof xs (p :: ps) 0) + (p :: ps).length) ::
          (occEndsAux fuel (p :: ps)
              (xs.drop
                (Int.toNat (native_seq_indexof xs (p :: ps) 0) +
                  (p :: ps).length))).map
            (· + (Int.toNat (native_seq_indexof xs (p :: ps) 0) +
              (p :: ps).length)) := by
  simp only [occEndsAux]

/-- The scan consumes at least the pattern, so any sufficient fuel gives the
same result. -/
theorem occEndsAux_congr (fuel₁ : Nat) :
    ∀ (fuel₂ : Nat) (pat xs : List SmtValue),
      xs.length < fuel₁ -> xs.length < fuel₂ ->
      occEndsAux fuel₁ pat xs = occEndsAux fuel₂ pat xs := by
  induction fuel₁ with
  | zero => intro fuel₂ pat xs h₁ h₂; omega
  | succ fuel₁ ih =>
      intro fuel₂ pat xs h₁ h₂
      cases fuel₂ with
      | zero => omega
      | succ fuel₂ =>
          cases pat with
          | nil => rw [occEndsAux_nil_pat, occEndsAux_nil_pat]
          | cons p ps =>
              rw [occEndsAux_succ, occEndsAux_succ]
              by_cases hIdxNeg : native_seq_indexof xs (p :: ps) 0 < 0
              · rw [if_pos hIdxNeg, if_pos hIdxNeg]
              · rw [if_neg hIdxNeg, if_neg hIdxNeg]
                have hNonneg : 0 ≤ native_seq_indexof xs (p :: ps) 0 :=
                  int_nonneg_of_not_neg hIdxNeg
                have hBounds :=
                  StrEqReplSupport.native_seq_indexof_zero_bounds_of_nonneg
                    xs (p :: ps) hNonneg
                have hPatPos : (p :: ps).length = ps.length + 1 := rfl
                have hDropLen :
                    (xs.drop
                        (Int.toNat (native_seq_indexof xs (p :: ps) 0) +
                          (p :: ps).length)).length <
                      fuel₁ := by
                  rw [List.length_drop]
                  omega
                have hDropLen₂ :
                    (xs.drop
                        (Int.toNat (native_seq_indexof xs (p :: ps) 0) +
                          (p :: ps).length)).length <
                      fuel₂ := by
                  rw [List.length_drop]
                  omega
                rw [ih fuel₂ (p :: ps) _ hDropLen hDropLen₂]

theorem occEndsAux_eq_occEnds (fuel : Nat) (pat xs : List SmtValue)
    (h : xs.length < fuel) :
    occEndsAux fuel pat xs = occEnds pat xs :=
  occEndsAux_congr fuel (xs.length + 1) pat xs h (by omega)

theorem positive_prefix_str_to_re_cons
    (p : SmtValue) (ps xs : List SmtValue) :
    native_re_positive_prefix_match_len? (native_str_to_re (p :: ps)) xs =
      if native_seq_prefix_eq (p :: ps) xs then
        some (p :: ps).length
      else
        none := by
  cases xs with
  | nil =>
      simp [native_re_positive_prefix_match_len?, native_str_to_re,
        native_seq_prefix_eq]
  | cons x xs =>
      rw [native_re_positive_prefix_match_len?.eq_2]
      change
        (match native_re_prefix_match_len?
            (native_re_deriv x (impl_native_re_of_list (p :: ps))) xs with
          | some n => some (n + 1)
          | none => none) = _
      rw [native_re_deriv_re_of_list_cons]
      by_cases hx : x = p
      · subst x
        rw [if_pos rfl, native_re_prefix_match_re_of_list]
        by_cases hPrefix : native_seq_prefix_eq ps xs = true
        · simp [native_seq_prefix_eq, native_veq, hPrefix]
        · simp [native_seq_prefix_eq, native_veq, hPrefix]
      · rw [if_neg hx]
        have hpx : p ≠ x := Ne.symm hx
        simp [native_re_prefix_match_len?, native_re_prefix_go_empty,
          native_seq_prefix_eq, native_veq, hx, hpx]

private theorem replace_aux_fuel_irrel
    (r : SmtRegLan) (replacement xs : List SmtValue)
    (fuel₁ fuel₂ : Nat)
    (h₁ : xs.length < fuel₁) (h₂ : xs.length < fuel₂) :
    impl_native_re_replace_all_nonempty_list_aux fuel₁ r replacement xs =
      impl_native_re_replace_all_nonempty_list_aux fuel₂ r replacement xs := by
  generalize hn : xs.length = n
  induction n using Nat.strongRecOn generalizing xs fuel₁ fuel₂ with
  | ind outerN ih =>
      cases fuel₁ with
      | zero => omega
      | succ fuel₁ =>
        cases fuel₂ with
        | zero => omega
        | succ fuel₂ =>
          cases xs with
          | nil =>
              simp [impl_native_re_replace_all_nonempty_list_aux,
                native_re_positive_prefix_match_len?]
          | cons c cs =>
              have hn' : cs.length + 1 = outerN := by
                simpa using hn
              rw [impl_native_re_replace_all_nonempty_list_aux.eq_3,
                impl_native_re_replace_all_nonempty_list_aux.eq_3]
              cases hPref :
                  native_re_positive_prefix_match_len? r (c :: cs) with
              | none =>
                  apply congrArg (List.cons c)
                  exact ih cs.length (by omega)
                    cs fuel₁ fuel₂ (by simpa using h₁)
                      (by simpa using h₂) rfl
              | some len =>
                  cases len with
                  | zero =>
                      apply congrArg (List.cons c)
                      exact ih cs.length (by omega)
                        cs fuel₁ fuel₂ (by simpa using h₁)
                          (by simpa using h₂) rfl
                  | succ k =>
                      apply congrArg (List.append replacement)
                      exact ih ((c :: cs).drop (k + 1)).length
                        (by
                          simp only [List.length_drop, List.length_cons]
                          omega)
                        ((c :: cs).drop (k + 1)) fuel₁ fuel₂
                        (by
                          simp only [List.length_drop, List.length_cons] at h₁ ⊢
                          omega)
                        (by
                          simp only [List.length_drop, List.length_cons] at h₂ ⊢
                          omega)
                        rfl

private theorem replace_aux_eq_replace_all_of_length_lt
    (r : SmtRegLan) (replacement xs : List SmtValue) (fuel : Nat)
    (hFuel : xs.length < fuel) :
    impl_native_re_replace_all_nonempty_list_aux fuel r replacement xs =
      impl_native_re_replace_all_nonempty_list r replacement xs := by
  unfold impl_native_re_replace_all_nonempty_list
  exact replace_aux_fuel_irrel r replacement xs fuel (xs.length + 1)
    hFuel (Nat.lt_succ_self xs.length)

/-! ## Scan-step unfoldings -/

theorem occEnds_eq_nil_of_indexof_neg (pat xs : List SmtValue)
    (h : native_seq_indexof xs pat 0 < 0) :
    occEnds pat xs = [] := by
  unfold occEnds occEndsAux
  cases pat with
  | nil => simp
  | cons p ps => simp [h]

theorem occEnds_step (pat xs : List SmtValue) (hPat : pat ≠ [])
    (h : 0 ≤ native_seq_indexof xs pat 0) :
    occEnds pat xs =
      (Int.toNat (native_seq_indexof xs pat 0) + pat.length) ::
        (occEnds pat
            (xs.drop
              (Int.toNat (native_seq_indexof xs pat 0) + pat.length))).map
          (· + (Int.toNat (native_seq_indexof xs pat 0) + pat.length)) := by
  have hBounds :=
    StrEqReplSupport.native_seq_indexof_zero_bounds_of_nonneg xs pat h
  have hNotNeg : ¬ native_seq_indexof xs pat 0 < 0 := Int.not_lt_of_ge h
  have hPatPos : 0 < pat.length := by
    cases pat with
    | nil => exact absurd rfl hPat
    | cons => simp
  have hDropLen :
      (xs.drop
          (Int.toNat (native_seq_indexof xs pat 0) + pat.length)).length <
        xs.length := by
    rw [List.length_drop]
    omega
  cases pat with
  | nil => exact absurd rfl hPat
  | cons p ps =>
      show occEndsAux (xs.length + 1) (p :: ps) xs = _
      rw [occEndsAux_succ, if_neg hNotNeg,
        occEndsAux_eq_occEnds xs.length (p :: ps) _ hDropLen]

theorem replace_all_eq_self_of_indexof_neg (pat repl xs : List SmtValue)
    (h : native_seq_indexof xs pat 0 < 0) :
    native_seq_replace_all xs pat repl = xs := by
  cases pat with
  | nil =>
      rw [StrEqReplSupport.native_seq_indexof_nil_zero] at h
      simp at h
  | cons p ps =>
      induction xs with
      | nil =>
          simp [native_seq_replace_all, native_str_replace_re_all,
            impl_native_re_replace_all_nonempty_list,
            impl_native_re_replace_all_nonempty_list_aux,
            native_re_positive_prefix_match_len?]
      | cons x xs ih =>
          have hPrefix : native_seq_prefix_eq (p :: ps) (x :: xs) = false := by
            cases hp : native_seq_prefix_eq (p :: ps) (x :: xs) with
            | false => rfl
            | true =>
                have hFit : (p :: ps).length ≤ (x :: xs).length :=
                  native_seq_prefix_eq_length_le (p :: ps) (x :: xs) hp
                have hFound := native_seq_indexof_zero_le_of_prefix_at
                  (x :: xs) (p :: ps) 0 (by simpa using hFit) (by simpa using hp)
                exact False.elim ((Int.not_lt_of_ge hFound.1) h)
          have hTailNeg : native_seq_indexof xs (p :: ps) 0 < 0 := by
            rcases native_seq_indexof_eq_neg_one_or_ge xs (p :: ps) 0 with
              hTailEq | hTailNonneg
            · rw [hTailEq]
              simp
            · let k := Int.toNat (native_seq_indexof xs (p :: ps) 0)
              have hTailBounds :=
                StrEqReplSupport.native_seq_indexof_zero_bounds_of_nonneg
                  xs (p :: ps) hTailNonneg
              have hTailPrefix := native_seq_prefix_eq_at_index_of_nonneg
                xs (p :: ps) hTailNonneg
              have hFullPrefix :
                  native_seq_prefix_eq (p :: ps)
                      ((x :: xs).drop (k + 1)) = true := by
                simpa [k, List.drop_succ_cons] using hTailPrefix
              have hFullFound := native_seq_indexof_zero_le_of_prefix_at
                (x :: xs) (p :: ps) (k + 1) (by
                  simpa [List.length_cons, Nat.add_assoc, Nat.add_comm,
                    Nat.add_left_comm] using Nat.succ_le_succ hTailBounds)
                hFullPrefix
              exact False.elim ((Int.not_lt_of_ge hFullFound.1) h)
          have hScan :
              native_seq_replace_all (x :: xs) (p :: ps) repl =
                x :: native_seq_replace_all xs (p :: ps) repl := by
            unfold native_seq_replace_all native_str_replace_re_all
              impl_native_re_replace_all_nonempty_list
            change impl_native_re_replace_all_nonempty_list_aux
                ((x :: xs).length + 1) (native_str_to_re (p :: ps)) repl
                  (x :: xs) = x :: native_seq_replace_all xs (p :: ps) repl
            rw [impl_native_re_replace_all_nonempty_list_aux.eq_3,
              positive_prefix_str_to_re_cons, hPrefix]
            rfl
          rw [hScan, ih hTailNeg]

theorem replace_all_nil_pat (repl xs : List SmtValue) :
    native_seq_replace_all xs [] repl = xs := by
  induction xs with
  | nil =>
      simp [native_seq_replace_all, native_str_replace_re_all,
        impl_native_re_replace_all_nonempty_list,
        impl_native_re_replace_all_nonempty_list_aux,
        native_re_positive_prefix_match_len?]
  | cons x xs ih =>
      unfold native_seq_replace_all native_str_replace_re_all
        impl_native_re_replace_all_nonempty_list
      change impl_native_re_replace_all_nonempty_list_aux
          ((x :: xs).length + 1) (native_str_to_re []) repl (x :: xs) =
        x :: xs
      rw [impl_native_re_replace_all_nonempty_list_aux.eq_3]
      have hPref :
          native_re_positive_prefix_match_len? (native_str_to_re [])
            (x :: xs) = none := by
        simp [native_str_to_re, impl_native_re_of_list,
          native_re_positive_prefix_match_len?, native_re_deriv,
          native_re_prefix_match_len?, native_re_prefix_go_empty]
      rw [hPref]
      change x :: native_seq_replace_all xs [] repl = x :: xs
      rw [ih]

theorem replace_all_step (pat repl xs : List SmtValue) (hPat : pat ≠ [])
    (h : 0 ≤ native_seq_indexof xs pat 0) :
    native_seq_replace_all xs pat repl =
      xs.take (Int.toNat (native_seq_indexof xs pat 0)) ++ repl ++
        native_seq_replace_all
          (xs.drop (Int.toNat (native_seq_indexof xs pat 0) + pat.length))
          pat repl := by
  cases pat with
  | nil => exact absurd rfl hPat
  | cons p ps =>
      induction xs with
      | nil =>
          rw [native_seq_indexof_eq_rec] at h
          simp [native_seq_prefix_eq] at h
      | cons x xs ih =>
          have hBounds :=
            StrEqReplSupport.native_seq_indexof_zero_bounds_of_nonneg
              (x :: xs) (p :: ps) h
          have hFullPrefix := native_seq_prefix_eq_at_index_of_nonneg
            (x :: xs) (p :: ps) h
          by_cases hPrefix : native_seq_prefix_eq (p :: ps) (x :: xs) = true
          · have hFit : (p :: ps).length ≤ (x :: xs).length :=
              native_seq_prefix_eq_length_le (p :: ps) (x :: xs) hPrefix
            have hFound := native_seq_indexof_zero_le_of_prefix_at
              (x :: xs) (p :: ps) 0 (by simpa using hFit) (by simpa using hPrefix)
            have hIdxZero : native_seq_indexof (x :: xs) (p :: ps) 0 = 0 := by
              exact Int.le_antisymm hFound.2 hFound.1
            have hDropLen :
                ((x :: xs).drop (p :: ps).length).length < (x :: xs).length := by
              rw [List.length_drop]
              simpa using Nat.lt_succ_of_le (Nat.sub_le xs.length ps.length)
            rw [hIdxZero]
            simp only [Int.toNat_zero, List.take_zero, List.nil_append,
              Nat.zero_add]
            unfold native_seq_replace_all native_str_replace_re_all
              impl_native_re_replace_all_nonempty_list
            change impl_native_re_replace_all_nonempty_list_aux
                ((x :: xs).length + 1) (native_str_to_re (p :: ps)) repl
                  (x :: xs) = _
            rw [impl_native_re_replace_all_nonempty_list_aux.eq_3,
              positive_prefix_str_to_re_cons, if_pos hPrefix]
            apply congrArg (List.append repl)
            exact replace_aux_eq_replace_all_of_length_lt
              (native_str_to_re (p :: ps)) repl
              ((x :: xs).drop (p :: ps).length) (x :: xs).length hDropLen
          · have hPrefixFalse :
                native_seq_prefix_eq (p :: ps) (x :: xs) = false := by
              cases hp : native_seq_prefix_eq (p :: ps) (x :: xs) <;>
                simp_all
            let n := Int.toNat (native_seq_indexof (x :: xs) (p :: ps) 0)
            have hnPos : 0 < n := by
              cases hn : n with
              | zero =>
                  have hAtZero :
                      native_seq_prefix_eq (p :: ps) (x :: xs) = true := by
                    simpa [n, hn] using hFullPrefix
                  rw [hPrefixFalse] at hAtZero
                  contradiction
              | succ m => omega
            have hDrop : xs.drop (n - 1) = (x :: xs).drop n := by
              cases hn : n with
              | zero => omega
              | succ m => simp [hn]
            have hTailPrefix :
                native_seq_prefix_eq (p :: ps) (xs.drop (n - 1)) = true := by
              rw [hDrop]
              simpa [n] using hFullPrefix
            have hTailFound := native_seq_indexof_zero_le_of_prefix_at
              xs (p :: ps) (n - 1) (by
                have hNBounds :
                    n + (p :: ps).length ≤ (x :: xs).length := by
                  simpa [n] using hBounds
                cases hn : n with
                | zero => omega
                | succ m =>
                    simp only [hn, Nat.succ_sub_one, List.length_cons]
                    simp only [hn, List.length_cons] at hNBounds
                    omega) hTailPrefix
            have hTailNonneg : 0 ≤ native_seq_indexof xs (p :: ps) 0 :=
              hTailFound.1
            let k := Int.toNat (native_seq_indexof xs (p :: ps) 0)
            have hTailBounds :=
              StrEqReplSupport.native_seq_indexof_zero_bounds_of_nonneg
                xs (p :: ps) hTailNonneg
            have hTailPrefixAt := native_seq_prefix_eq_at_index_of_nonneg
              xs (p :: ps) hTailNonneg
            have hFullPrefixAt :
                native_seq_prefix_eq (p :: ps) ((x :: xs).drop (k + 1)) = true := by
              simpa [k, List.drop_succ_cons] using hTailPrefixAt
            have hFullFound := native_seq_indexof_zero_le_of_prefix_at
              (x :: xs) (p :: ps) (k + 1) (by
                simpa [List.length_cons, Nat.add_assoc, Nat.add_comm,
                  Nat.add_left_comm] using Nat.succ_le_succ hTailBounds)
              hFullPrefixAt
            have hFullCast :
                Int.ofNat n = native_seq_indexof (x :: xs) (p :: ps) 0 := by
              exact Int.toNat_of_nonneg h
            have hTailCast :
                Int.ofNat k = native_seq_indexof xs (p :: ps) 0 := by
              exact Int.toNat_of_nonneg hTailNonneg
            have hkLe : k ≤ n - 1 := by
              have hCastLe := hTailFound.2
              rw [← hTailCast] at hCastLe
              apply Int.ofNat_le.mp
              exact hCastLe
            have hnLe : n ≤ k + 1 := by
              have hCastLe := hFullFound.2
              rw [← hFullCast] at hCastLe
              apply Int.ofNat_le.mp
              exact hCastLe
            have hNatShift : n = k + 1 := by omega
            have hDropShift :
                (x :: xs).drop ((k + 1) + (p :: ps).length) =
                  xs.drop (k + (p :: ps).length) := by
              rw [show (k + 1) + (p :: ps).length =
                  (k + (p :: ps).length) + 1 by omega]
              simp
            have hScan :
                native_seq_replace_all (x :: xs) (p :: ps) repl =
                  x :: native_seq_replace_all xs (p :: ps) repl := by
              unfold native_seq_replace_all native_str_replace_re_all
                impl_native_re_replace_all_nonempty_list
              change impl_native_re_replace_all_nonempty_list_aux
                  ((x :: xs).length + 1) (native_str_to_re (p :: ps)) repl
                    (x :: xs) = x :: native_seq_replace_all xs (p :: ps) repl
              rw [impl_native_re_replace_all_nonempty_list_aux.eq_3,
                positive_prefix_str_to_re_cons, hPrefixFalse]
              rfl
            rw [hScan]
            have hTailStep := ih hTailNonneg
            have hFullNat :
                Int.toNat (native_seq_indexof (x :: xs) (p :: ps) 0) =
                  k + 1 := by
              simpa [n] using hNatShift
            rw [hFullNat, hDropShift]
            simpa [k, List.take_succ_cons] using
                congrArg (List.cons x) hTailStep

theorem replace_all_cons_of_not_prefix
    (pat repl : List SmtValue) (x : SmtValue) (xs : List SmtValue)
    (hPat : pat ≠ [])
    (hPrefix : native_seq_prefix_eq pat (x :: xs) = false) :
    native_seq_replace_all (x :: xs) pat repl =
      x :: native_seq_replace_all xs pat repl := by
  cases pat with
  | nil => exact absurd rfl hPat
  | cons p ps =>
      unfold native_seq_replace_all native_str_replace_re_all
        impl_native_re_replace_all_nonempty_list
      change impl_native_re_replace_all_nonempty_list_aux
          ((x :: xs).length + 1) (native_str_to_re (p :: ps)) repl
            (x :: xs) = x :: native_seq_replace_all xs (p :: ps) repl
      rw [impl_native_re_replace_all_nonempty_list_aux.eq_3,
        positive_prefix_str_to_re_cons, hPrefix]
      rfl

theorem replace_all_id (pat xs : List SmtValue) :
    native_seq_replace_all xs pat pat = xs := by
  cases pat with
  | nil => exact replace_all_nil_pat [] xs
  | cons p ps =>
      suffices hGen : ∀ (len : Nat) (ys : List SmtValue), ys.length = len ->
          native_seq_replace_all ys (p :: ps) (p :: ps) = ys by
        exact hGen xs.length xs rfl
      intro len
      induction len using Nat.strongRecOn with
      | ind len ih =>
          intro ys hLen
          by_cases hNeg : native_seq_indexof ys (p :: ps) 0 < 0
          · exact replace_all_eq_self_of_indexof_neg (p :: ps) (p :: ps) ys hNeg
          · have hNonneg : 0 ≤ native_seq_indexof ys (p :: ps) 0 :=
              int_nonneg_of_not_neg hNeg
            have hBounds :=
              StrEqReplSupport.native_seq_indexof_zero_bounds_of_nonneg
                ys (p :: ps) hNonneg
            have hTailLt :
                (ys.drop
                    (Int.toNat (native_seq_indexof ys (p :: ps) 0) +
                      (p :: ps).length)).length < len := by
              rw [List.length_drop, ← hLen]
              simp only [List.length_cons] at hBounds ⊢
              omega
            rw [replace_all_step (p :: ps) (p :: ps) ys (by simp) hNonneg,
              ih _ hTailLt _ rfl]
            exact StrEqReplSupport.native_seq_indexof_zero_decomp_take_drop
              ys (p :: ps) hNonneg

theorem replace_all_self_of_nonempty
    (xs repl : List SmtValue) (hXs : xs ≠ []) :
    native_seq_replace_all xs xs repl = repl := by
  have hIdx : native_seq_indexof xs xs 0 = 0 :=
    native_seq_indexof_self_zero xs
  have hNonneg : 0 ≤ native_seq_indexof xs xs 0 := by simp [hIdx]
  have hEmptyIdx : native_seq_indexof [] xs 0 = -1 := by
    rw [native_seq_indexof_eq_rec]
    simp [hXs]
  have hEmpty : native_seq_replace_all [] xs repl = [] :=
    replace_all_eq_self_of_indexof_neg xs repl [] (by rw [hEmptyIdx]; simp)
  rw [replace_all_step xs repl xs hXs hNonneg, hIdx]
  simp [hEmpty]

/-! ## Element bounds and sortedness -/

theorem occEnds_mem_bounds (pat : List SmtValue) (xs : List SmtValue)
    (e : Nat) (hMem : e ∈ occEnds pat xs) :
    pat.length ≤ e ∧ e ≤ xs.length := by
  suffices hGen : ∀ (len : Nat) (ys : List SmtValue), ys.length = len ->
      ∀ e : Nat, e ∈ occEnds pat ys -> pat.length ≤ e ∧ e ≤ ys.length by
    exact hGen xs.length xs rfl e hMem
  intro len
  induction len using Nat.strongRecOn with
  | ind len ih =>
      intro ys hLen e hMem
      by_cases hPatNil : pat = []
      · subst hPatNil; rw [occEnds_nil_pat] at hMem; cases hMem
      by_cases hNeg : native_seq_indexof ys pat 0 < 0
      · rw [occEnds_eq_nil_of_indexof_neg pat ys hNeg] at hMem; cases hMem
      have hNonneg : 0 ≤ native_seq_indexof ys pat 0 :=
        int_nonneg_of_not_neg hNeg
      have hBounds :=
        StrEqReplSupport.native_seq_indexof_zero_bounds_of_nonneg
          ys pat hNonneg
      have hPatPos : 0 < pat.length := by
        cases pat with
        | nil => exact absurd rfl hPatNil
        | cons => simp
      rw [occEnds_step pat ys hPatNil hNonneg] at hMem
      rcases List.mem_cons.mp hMem with hHead | hTail
      · subst hHead
        constructor
        · omega
        · omega
      · rcases List.mem_map.mp hTail with ⟨e', hMem', rfl⟩
        have hDropLt :
            (ys.drop
                (Int.toNat (native_seq_indexof ys pat 0) +
                  pat.length)).length < len := by
          rw [List.length_drop]; omega
        have hRec := ih _ hDropLt
          (ys.drop
            (Int.toNat (native_seq_indexof ys pat 0) + pat.length))
          rfl e' hMem'
        rw [List.length_drop] at hRec
        constructor
        · omega
        · omega

theorem occEnds_pairwise (pat : List SmtValue) (xs : List SmtValue) :
    (occEnds pat xs).Pairwise (· < ·) := by
  suffices hGen : ∀ (len : Nat) (ys : List SmtValue), ys.length = len ->
      (occEnds pat ys).Pairwise (· < ·) by
    exact hGen xs.length xs rfl
  intro len
  induction len using Nat.strongRecOn with
  | ind len ih =>
      intro ys hLen
      by_cases hPatNil : pat = []
      · subst hPatNil; rw [occEnds_nil_pat]; exact List.Pairwise.nil
      by_cases hNeg : native_seq_indexof ys pat 0 < 0
      · rw [occEnds_eq_nil_of_indexof_neg pat ys hNeg]
        exact List.Pairwise.nil
      have hNonneg : 0 ≤ native_seq_indexof ys pat 0 :=
        int_nonneg_of_not_neg hNeg
      have hBounds :=
        StrEqReplSupport.native_seq_indexof_zero_bounds_of_nonneg
          ys pat hNonneg
      have hPatPos : 0 < pat.length := by
        cases pat with
        | nil => exact absurd rfl hPatNil
        | cons => simp
      rw [occEnds_step pat ys hPatNil hNonneg]
      have hDropLt :
          (ys.drop
              (Int.toNat (native_seq_indexof ys pat 0) +
                pat.length)).length < len := by
        rw [List.length_drop]; omega
      have hRecPairwise := ih _ hDropLt
        (ys.drop (Int.toNat (native_seq_indexof ys pat 0) + pat.length)) rfl
      constructor
      · intro e hMem
        rcases List.mem_map.mp hMem with ⟨e', hMem', rfl⟩
        have hE' := occEnds_mem_bounds pat
          (ys.drop (Int.toNat (native_seq_indexof ys pat 0) + pat.length))
          e' hMem'
        omega
      · rw [List.pairwise_map]
        exact hRecPairwise.imp (by intro a b hab; omega)

/-! ## Prefix-match transfer across `take` -/

theorem prefix_eq_length_le (pat : List SmtValue) :
    ∀ ys : List SmtValue, native_seq_prefix_eq pat ys = true ->
      pat.length ≤ ys.length := by
  induction pat with
  | nil => intro ys _; simp
  | cons p ps ih =>
      intro ys h
      cases ys with
      | nil => simp [native_seq_prefix_eq] at h
      | cons y ys' =>
          have hParts : native_veq p y = true ∧
              native_seq_prefix_eq ps ys' = true := by
            simpa [native_seq_prefix_eq, Bool.and_eq_true] using h
          have := ih ys' hParts.2
          simpa using Nat.succ_le_succ this

theorem prefix_eq_of_prefix_take (pat : List SmtValue) :
    ∀ (ys : List SmtValue) (t : Nat),
      native_seq_prefix_eq pat (ys.take t) = true ->
      native_seq_prefix_eq pat ys = true := by
  induction pat with
  | nil => intro ys t _; simp [native_seq_prefix_eq]
  | cons p ps ih =>
      intro ys t h
      cases ys with
      | nil => simp [native_seq_prefix_eq] at h
      | cons y ys' =>
          cases t with
          | zero => simp [native_seq_prefix_eq] at h
          | succ t' =>
              have hParts : native_veq p y = true ∧
                  native_seq_prefix_eq ps (ys'.take t') = true := by
                simpa [List.take_succ_cons, native_seq_prefix_eq,
                  Bool.and_eq_true] using h
              have hRec := ih ys' t' hParts.2
              simp [native_seq_prefix_eq, Bool.and_eq_true, hParts.1, hRec]

theorem prefix_eq_take_of_prefix (pat : List SmtValue) :
    ∀ (ys : List SmtValue) (t : Nat),
      native_seq_prefix_eq pat ys = true -> pat.length ≤ t ->
      native_seq_prefix_eq pat (ys.take t) = true := by
  induction pat with
  | nil => intro ys t _ _; simp [native_seq_prefix_eq]
  | cons p ps ih =>
      intro ys t h hLen
      cases ys with
      | nil => simp [native_seq_prefix_eq] at h
      | cons y ys' =>
          cases t with
          | zero => simp at hLen
          | succ t' =>
              have hParts : native_veq p y = true ∧
                  native_seq_prefix_eq ps ys' = true := by
                simpa [native_seq_prefix_eq, Bool.and_eq_true] using h
              have hRec := ih ys' t' hParts.2 (by simpa using hLen)
              simp [List.take_succ_cons, native_seq_prefix_eq,
                Bool.and_eq_true, hParts.1, hRec]

/-! ## `indexof` under `take` -/

/-- A found index is a genuine prefix match with room to fit. -/
theorem indexof_decomp_of_nonneg (xs pat : List SmtValue)
    (h : 0 ≤ native_seq_indexof xs pat 0) :
    native_seq_prefix_eq pat
        (xs.drop (Int.toNat (native_seq_indexof xs pat 0))) = true ∧
      Int.toNat (native_seq_indexof xs pat 0) + pat.length ≤ xs.length :=
  ⟨native_seq_prefix_eq_at_index_of_nonneg xs pat h,
    StrEqReplSupport.native_seq_indexof_zero_bounds_of_nonneg xs pat h⟩

theorem indexof_take_eq_of_fit (xs pat : List SmtValue) (m : Nat)
    (hNonneg : 0 ≤ native_seq_indexof xs pat 0)
    (hFit : Int.toNat (native_seq_indexof xs pat 0) + pat.length ≤ m) :
    native_seq_indexof (xs.take m) pat 0 = native_seq_indexof xs pat 0 := by
  rcases indexof_decomp_of_nonneg xs pat hNonneg with ⟨hPrefix, hBounds⟩
  -- the same match exists inside `xs.take m`
  have hDropTake :
      (xs.take m).drop (Int.toNat (native_seq_indexof xs pat 0)) =
        (xs.drop (Int.toNat (native_seq_indexof xs pat 0))).take
          (m - Int.toNat (native_seq_indexof xs pat 0)) := by
    rw [List.drop_take]
  have hPrefixTake :
      native_seq_prefix_eq pat
          ((xs.take m).drop
            (Int.toNat (native_seq_indexof xs pat 0))) = true := by
    rw [hDropTake]
    exact prefix_eq_take_of_prefix pat _ _ hPrefix (by omega)
  have hFitTake :
      Int.toNat (native_seq_indexof xs pat 0) + pat.length ≤
        (xs.take m).length := by
    rw [List.length_take]
    omega
  have hUpper :=
    native_seq_indexof_zero_le_of_prefix_at
      (xs.take m) pat _ hFitTake hPrefixTake
  -- any earlier match inside `xs.take m` would be an earlier match in `xs`
  have hNonneg' : 0 ≤ native_seq_indexof (xs.take m) pat 0 := hUpper.1
  rcases indexof_decomp_of_nonneg (xs.take m) pat hNonneg' with
    ⟨hPrefix', hBounds'⟩
  have hTakeLenLe : (xs.take m).length ≤ xs.length := by
    rw [List.length_take]; omega
  have hPrefixXs :
      native_seq_prefix_eq pat
          (xs.drop
            (Int.toNat (native_seq_indexof (xs.take m) pat 0))) = true := by
    apply prefix_eq_of_prefix_take pat _
      (m - Int.toNat (native_seq_indexof (xs.take m) pat 0))
    rw [← List.drop_take]
    exact hPrefix'
  have hFitXs :
      Int.toNat (native_seq_indexof (xs.take m) pat 0) + pat.length ≤
        xs.length := by
    omega
  have hLower :=
    native_seq_indexof_zero_le_of_prefix_at
      xs pat _ hFitXs hPrefixXs
  -- `≤` both ways forces equality
  have h₁ := hUpper.2
  have h₂ := hLower.2
  rw [Int.ofNat_eq_natCast] at h₁ h₂
  unfold native_Int at *
  omega

theorem indexof_take_neg (xs pat : List SmtValue) (m : Nat)
    (hPat : pat ≠ [])
    (h : native_seq_indexof xs pat 0 < 0 ∨
      m < Int.toNat (native_seq_indexof xs pat 0) + pat.length) :
    native_seq_indexof (xs.take m) pat 0 < 0 := by
  by_cases hNeg : native_seq_indexof (xs.take m) pat 0 < 0
  · exact hNeg
  exfalso
  have hNonneg' : 0 ≤ native_seq_indexof (xs.take m) pat 0 :=
    int_nonneg_of_not_neg hNeg
  rcases indexof_decomp_of_nonneg (xs.take m) pat hNonneg' with
    ⟨hPrefix', hBounds'⟩
  have hTakeLenLe : (xs.take m).length ≤ xs.length := by
    rw [List.length_take]; omega
  have hTakeLenLeM : (xs.take m).length ≤ m := by
    rw [List.length_take]; omega
  have hPrefixXs :
      native_seq_prefix_eq pat
          (xs.drop
            (Int.toNat (native_seq_indexof (xs.take m) pat 0))) = true := by
    apply prefix_eq_of_prefix_take pat _
      (m - Int.toNat (native_seq_indexof (xs.take m) pat 0))
    rw [← List.drop_take]
    exact hPrefix'
  have hFitXs :
      Int.toNat (native_seq_indexof (xs.take m) pat 0) + pat.length ≤
        xs.length := by
    omega
  have hLower :=
    native_seq_indexof_zero_le_of_prefix_at
      xs pat _ hFitXs hPrefixXs
  have hNonneg : 0 ≤ native_seq_indexof xs pat 0 := hLower.1
  rcases h with hNegXs | hRoom
  · unfold native_Int at *
    omega
  · -- the original first match starts no later, so it also fits within `m`
    have h₂ := hLower.2
    rw [Int.ofNat_eq_natCast] at h₂
    unfold native_Int at *
    omega

/-! ## Occurrence ends of a prefix -/

theorem filter_le_eq_nil_of_all_gt (L : List Nat) (m : Nat)
    (h : ∀ e ∈ L, m < e) :
    L.filter (fun e => decide (e ≤ m)) = [] := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      have ha : m < a := h a (List.mem_cons_self ..)
      have hNotLe : ¬ a ≤ m := by omega
      simp only [List.filter_cons, decide_eq_true_eq]
      rw [if_neg (by simpa using hNotLe)]
      exact ih (fun e he => h e (List.mem_cons_of_mem a he))

theorem filter_le_map_add (L : List Nat) (a m : Nat) :
    (L.map (· + a)).filter (fun e => decide (e ≤ m)) =
      (L.filter (fun e => decide (e + a ≤ m))).map (· + a) := by
  induction L with
  | nil => rfl
  | cons b L ih =>
      simp only [List.map_cons, List.filter_cons]
      by_cases hb : b + a ≤ m
      · rw [if_pos (by simpa using hb), if_pos (by simpa using hb)]
        simp [ih]
      · rw [if_neg (by simpa using hb), if_neg (by simpa using hb)]
        exact ih

/-- The occurrences of a prefix of `xs` are exactly the occurrences of `xs`
ending within the prefix. -/
theorem occEnds_take (pat xs : List SmtValue) (m : Nat) (hPat : pat ≠ []) :
    occEnds pat (xs.take m) =
      (occEnds pat xs).filter (fun e => decide (e ≤ m)) := by
  suffices hGen : ∀ (len : Nat) (ys : List SmtValue), ys.length = len ->
      ∀ m : Nat, occEnds pat (ys.take m) =
        (occEnds pat ys).filter (fun e => decide (e ≤ m)) by
    exact hGen xs.length xs rfl m
  intro len
  induction len using Nat.strongRecOn with
  | ind len ih =>
      intro ys hLen m
      have hPatPos : 0 < pat.length := by
        cases pat with
        | nil => exact absurd rfl hPat
        | cons => simp
      by_cases hNeg : native_seq_indexof ys pat 0 < 0
      · rw [occEnds_eq_nil_of_indexof_neg pat ys hNeg]
        rw [occEnds_eq_nil_of_indexof_neg pat (ys.take m)
          (indexof_take_neg ys pat m hPat (Or.inl hNeg))]
        rfl
      have hNonneg : 0 ≤ native_seq_indexof ys pat 0 :=
        int_nonneg_of_not_neg hNeg
      have hBounds :=
        StrEqReplSupport.native_seq_indexof_zero_bounds_of_nonneg
          ys pat hNonneg
      rw [occEnds_step pat ys hPat hNonneg]
      by_cases hRoom :
          Int.toNat (native_seq_indexof ys pat 0) + pat.length ≤ m
      · -- the first occurrence also lies inside the prefix
        have hIdxTake := indexof_take_eq_of_fit ys pat m hNonneg hRoom
        have hIdxTakeNonneg : 0 ≤ native_seq_indexof (ys.take m) pat 0 := by
          rw [hIdxTake]; exact hNonneg
        rw [occEnds_step pat (ys.take m) hPat hIdxTakeNonneg]
        rw [hIdxTake]
        have hDropTake :
            (ys.take m).drop
                (Int.toNat (native_seq_indexof ys pat 0) + pat.length) =
              (ys.drop
                  (Int.toNat (native_seq_indexof ys pat 0) +
                    pat.length)).take
                (m -
                  (Int.toNat (native_seq_indexof ys pat 0) +
                    pat.length)) := by
          rw [List.drop_take]
        rw [hDropTake]
        have hDropLt :
            (ys.drop
                (Int.toNat (native_seq_indexof ys pat 0) +
                  pat.length)).length < len := by
          rw [List.length_drop]; omega
        rw [ih _ hDropLt
          (ys.drop (Int.toNat (native_seq_indexof ys pat 0) + pat.length))
          rfl
          (m - (Int.toNat (native_seq_indexof ys pat 0) + pat.length))]
        rw [List.filter_cons]
        rw [if_pos (by simpa using hRoom)]
        rw [filter_le_map_add]
        congr 1
        apply congrArg (List.map _)
        apply List.filter_congr
        intro e hMem
        have hE := occEnds_mem_bounds pat
          (ys.drop (Int.toNat (native_seq_indexof ys pat 0) + pat.length))
          e hMem
        simp only [decide_eq_decide]
        omega
      · -- the prefix cuts the first occurrence off
        rw [occEnds_eq_nil_of_indexof_neg pat (ys.take m)
          (indexof_take_neg ys pat m hPat (Or.inr (by omega)))]
        rw [List.filter_cons]
        rw [if_neg (by simpa using hRoom)]
        rw [filter_le_eq_nil_of_all_gt]
        intro e hMem
        rcases List.mem_map.mp hMem with ⟨e', hMem', rfl⟩
        have hE' := occEnds_mem_bounds pat
          (ys.drop (Int.toNat (native_seq_indexof ys pat 0) + pat.length))
          e' hMem'
        omega

/-! ## Counting in sorted lists -/

theorem filter_eq_nil_of_forall_false {α : Type} (p : α -> Bool)
    (L : List α) (h : ∀ e ∈ L, p e = false) : L.filter p = [] := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      simp only [List.filter_cons, h a (List.mem_cons_self ..)]
      exact ih (fun e he => h e (List.mem_cons_of_mem a he))

theorem filter_le_length_mono (L : List Nat) {m₁ m₂ : Nat} (h : m₁ ≤ m₂) :
    (L.filter (fun e => decide (e ≤ m₁))).length ≤
      (L.filter (fun e => decide (e ≤ m₂))).length := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.filter_cons]
      by_cases h₁ : a ≤ m₁
      · rw [if_pos (by simpa using h₁),
          if_pos (by simp; omega)]
        simpa using ih
      · rw [if_neg (by simpa using h₁)]
        by_cases h₂ : a ≤ m₂
        · rw [if_pos (by simpa using h₂)]
          simp only [List.length_cons]
          exact Nat.le_succ_of_le ih
        · rw [if_neg (by simpa using h₂)]
          exact ih

theorem getD_mem_of_lt (L : List Nat) (n : Nat) (hn : n < L.length) :
    L.getD n 0 ∈ L := by
  induction L generalizing n with
  | nil => simp at hn
  | cons a L ih =>
      cases n with
      | zero => simp
      | succ n =>
          simp only [List.getD_cons_succ]
          exact List.mem_cons_of_mem a (ih n (by simpa using hn))

theorem getD_map_add (L : List Nat) (a n : Nat) (hn : n < L.length) :
    (L.map (· + a)).getD n 0 = L.getD n 0 + a := by
  induction L generalizing n with
  | nil => simp at hn
  | cons b L ih =>
      cases n with
      | zero => simp
      | succ n =>
          simp only [List.map_cons, List.getD_cons_succ]
          exact ih n (by simpa using hn)

theorem pairwise_getD_lt (L : List Nat) (hPW : L.Pairwise (· < ·)) :
    ∀ i j : Nat, i < j -> j < L.length -> L.getD i 0 < L.getD j 0 := by
  induction L with
  | nil => intro i j _ hj; simp at hj
  | cons a L ih =>
      intro i j hij hj
      have hHead : ∀ e ∈ L, a < e := (List.pairwise_cons.mp hPW).1
      have hPW' := (List.pairwise_cons.mp hPW).2
      cases i with
      | zero =>
          cases j with
          | zero => omega
          | succ j =>
              simp only [List.getD_cons_zero, List.getD_cons_succ]
              exact hHead _ (getD_mem_of_lt L j (by simpa using hj))
      | succ i =>
          cases j with
          | zero => omega
          | succ j =>
              simp only [List.getD_cons_succ]
              exact ih hPW' i j (by omega) (by simpa using hj)

theorem filter_le_getD_length (L : List Nat) (hPW : L.Pairwise (· < ·)) :
    ∀ n : Nat, n < L.length ->
      (L.filter (fun e => decide (e ≤ L.getD n 0))).length = n + 1 := by
  induction L with
  | nil => intro n hn; simp at hn
  | cons a L ih =>
      intro n hn
      have hHead : ∀ e ∈ L, a < e := (List.pairwise_cons.mp hPW).1
      have hPW' := (List.pairwise_cons.mp hPW).2
      cases n with
      | zero =>
          simp only [List.getD_cons_zero, List.filter_cons]
          rw [if_pos (by simp)]
          rw [filter_le_eq_nil_of_all_gt L a hHead]
          rfl
      | succ n =>
          have hn' : n < L.length := by simpa using hn
          have hMem := getD_mem_of_lt L n hn'
          have hALe : a ≤ L.getD n 0 := Nat.le_of_lt (hHead _ hMem)
          simp only [List.getD_cons_succ, List.filter_cons]
          rw [if_pos (by simpa using hALe)]
          simp only [List.length_cons]
          rw [ih hPW' n hn']

theorem filter_lt_getD_length (L : List Nat) (hPW : L.Pairwise (· < ·)) :
    ∀ n : Nat, n < L.length ->
      (L.filter (fun e => decide (e < L.getD n 0))).length = n := by
  induction L with
  | nil => intro n hn; simp at hn
  | cons a L ih =>
      intro n hn
      have hHead : ∀ e ∈ L, a < e := (List.pairwise_cons.mp hPW).1
      have hPW' := (List.pairwise_cons.mp hPW).2
      cases n with
      | zero =>
          simp only [List.getD_cons_zero, List.filter_cons]
          rw [if_neg (by simp)]
          rw [filter_eq_nil_of_forall_false _ L
            (fun e he => by
              have := hHead e he
              simp only [decide_eq_false_iff_not]
              omega)]
          rfl
      | succ n =>
          have hn' : n < L.length := by simpa using hn
          have hMem := getD_mem_of_lt L n hn'
          have hALt : a < L.getD n 0 := hHead _ hMem
          simp only [List.getD_cons_succ, List.filter_cons]
          rw [if_pos (by simpa using hALt)]
          simp only [List.length_cons]
          rw [ih hPW' n hn']

/-! ## Scan boundaries -/

/-- Scan boundaries: `bound pat xs 0 = 0`, and `bound pat xs (n + 1)` is the
end position of the `(n + 1)`-st greedy occurrence of `pat` in `xs`. -/
@[expose] def bound (pat xs : List SmtValue) (n : Nat) : Nat :=
  (0 :: occEnds pat xs).getD n 0

theorem bound_zero (pat xs : List SmtValue) : bound pat xs 0 = 0 := rfl

theorem bound_succ (pat xs : List SmtValue) (n : Nat) :
    bound pat xs (n + 1) = (occEnds pat xs).getD n 0 := rfl

theorem bound_mem (pat xs : List SmtValue) (n : Nat) (h1 : 1 ≤ n)
    (h2 : n ≤ (occEnds pat xs).length) :
    bound pat xs n ∈ occEnds pat xs := by
  cases n with
  | zero => omega
  | succ n =>
      rw [bound_succ]
      exact getD_mem_of_lt _ n (by omega)

theorem bound_le_len (pat xs : List SmtValue) (n : Nat)
    (h : n ≤ (occEnds pat xs).length) :
    bound pat xs n ≤ xs.length := by
  cases n with
  | zero => simp [bound_zero]
  | succ n =>
      exact (occEnds_mem_bounds pat xs _
        (bound_mem pat xs (n + 1) (by omega) h)).2

theorem bound_ge_pat (pat xs : List SmtValue) (n : Nat) (h1 : 1 ≤ n)
    (h2 : n ≤ (occEnds pat xs).length) :
    pat.length ≤ bound pat xs n :=
  (occEnds_mem_bounds pat xs _ (bound_mem pat xs n h1 h2)).1

/-! ## Counting occurrences of prefixes at the boundaries -/

theorem occ_count_at_bound (pat xs : List SmtValue) (hPat : pat ≠ [])
    (n : Nat) (hn : n ≤ (occEnds pat xs).length) :
    (occEnds pat (xs.take (bound pat xs n))).length = n := by
  rw [occEnds_take pat xs _ hPat]
  cases n with
  | zero =>
      rw [bound_zero, filter_le_eq_nil_of_all_gt _ 0
        (fun e he => by
          have := occEnds_mem_bounds pat xs e he
          have hPatPos : 0 < pat.length := by
            cases pat with
            | nil => exact absurd rfl hPat
            | cons => simp
          omega)]
      rfl
  | succ n =>
      rw [bound_succ]
      exact filter_le_getD_length _ (occEnds_pairwise pat xs) n (by omega)

theorem occ_count_below_bound (pat xs : List SmtValue) (hPat : pat ≠ [])
    (n : Nat) (h1 : 1 ≤ n) (hn : n ≤ (occEnds pat xs).length) :
    (occEnds pat (xs.take (bound pat xs n - 1))).length = n - 1 := by
  rw [occEnds_take pat xs _ hPat]
  have hBPos : 1 ≤ bound pat xs n := by
    have := bound_ge_pat pat xs n h1 hn
    have hPatPos : 0 < pat.length := by
      cases pat with
      | nil => exact absurd rfl hPat
      | cons => simp
    omega
  have hCongr :
      (occEnds pat xs).filter
          (fun e => decide (e ≤ bound pat xs n - 1)) =
        (occEnds pat xs).filter (fun e => decide (e < bound pat xs n)) := by
    apply List.filter_congr
    intro e _
    simp only [decide_eq_decide]
    omega
  rw [hCongr]
  cases n with
  | zero => omega
  | succ n =>
      rw [bound_succ]
      have := filter_lt_getD_length _ (occEnds_pairwise pat xs) n (by omega)
      omega

/-- Uniqueness of the `@strings_occur_index` choice witness: any nonnegative
`v` whose prefix contains exactly `n` occurrences, minimally so, is the `n`-th
scan boundary. -/
theorem occ_count_unique (pat xs : List SmtValue) (hPat : pat ≠ [])
    (n : Nat) (hn : n ≤ (occEnds pat xs).length) (v : Int) (hv : 0 ≤ v)
    (hEq : (occEnds pat (xs.take (Int.toNat v))).length = n)
    (hPrev : v = 0 ∨
      (occEnds pat (xs.take (Int.toNat (v - 1)))).length < n) :
    v = ((bound pat xs n : Nat) : Int) := by
  have hPatPos : 0 < pat.length := by
    cases pat with
    | nil => exact absurd rfl hPat
    | cons => simp
  cases n with
  | zero =>
      rcases hPrev with hv0 | hLt
      · rw [hv0, bound_zero]; norm_cast
      · omega
  | succ n =>
      -- `v = 0` is impossible: the empty prefix has no occurrences
      have hvNe : v ≠ 0 := by
        intro hv0
        rw [hv0] at hEq
        have h0 : (occEnds pat (xs.take (Int.toNat (0 : Int)))).length = 0 := by
          rw [occEnds_take pat xs _ hPat]
          rw [filter_le_eq_nil_of_all_gt _ _
            (fun e he => by
              have := occEnds_mem_bounds pat xs e he
              omega)]
          rfl
        omega
      rcases hPrev with hv0 | hLt
      · exact absurd hv0 hvNe
      have hv1 : 1 ≤ v := by omega
      rw [occEnds_take pat xs _ hPat] at hEq hLt
      have hAt := occ_count_at_bound pat xs hPat (n + 1) hn
      rw [occEnds_take pat xs _ hPat] at hAt
      have hBelow := occ_count_below_bound pat xs hPat (n + 1) (by omega) hn
      rw [occEnds_take pat xs _ hPat] at hBelow
      have hBPos : 1 ≤ bound pat xs (n + 1) := by
        have := bound_ge_pat pat xs (n + 1) (by omega) hn
        omega
      by_cases hLtB : Int.toNat v < bound pat xs (n + 1)
      · exfalso
        have hMono := filter_le_length_mono (occEnds pat xs)
          (show Int.toNat v ≤ bound pat xs (n + 1) - 1 by omega)
        omega
      by_cases hGtB : bound pat xs (n + 1) < Int.toNat v
      · exfalso
        have hMono := filter_le_length_mono (occEnds pat xs)
          (show bound pat xs (n + 1) ≤ Int.toNat (v - 1) by omega)
        omega
      have hEqB : Int.toNat v = bound pat xs (n + 1) := by omega
      omega

/-! ## Length arithmetic for `replace_all` -/

theorem replace_all_length_int (pat repl xs : List SmtValue)
    (hPat : pat ≠ []) :
    ((native_seq_replace_all xs pat repl).length : Int) =
      (xs.length : Int) +
        ((occEnds pat xs).length : Int) *
          ((repl.length : Int) - (pat.length : Int)) := by
  suffices hGen : ∀ (len : Nat) (ys : List SmtValue), ys.length = len ->
      ((native_seq_replace_all ys pat repl).length : Int) =
        (ys.length : Int) +
          ((occEnds pat ys).length : Int) *
            ((repl.length : Int) - (pat.length : Int)) by
    exact hGen xs.length xs rfl
  intro len
  induction len using Nat.strongRecOn with
  | ind len ih =>
      intro ys hLen
      have hPatPos : 0 < pat.length := by
        cases pat with
        | nil => exact absurd rfl hPat
        | cons => simp
      by_cases hNeg : native_seq_indexof ys pat 0 < 0
      · rw [replace_all_eq_self_of_indexof_neg pat repl ys hNeg,
          occEnds_eq_nil_of_indexof_neg pat ys hNeg]
        simp
      have hNonneg : 0 ≤ native_seq_indexof ys pat 0 :=
        int_nonneg_of_not_neg hNeg
      have hBounds :=
        StrEqReplSupport.native_seq_indexof_zero_bounds_of_nonneg
          ys pat hNonneg
      rw [replace_all_step pat repl ys hPat hNonneg,
        occEnds_step pat ys hPat hNonneg]
      have hDropLt :
          (ys.drop
              (Int.toNat (native_seq_indexof ys pat 0) +
                pat.length)).length < len := by
        rw [List.length_drop]; omega
      have hRec := ih _ hDropLt
        (ys.drop (Int.toNat (native_seq_indexof ys pat 0) + pat.length)) rfl
      simp only [List.length_append, List.length_cons, List.length_map,
        List.length_take, List.length_drop] at hRec ⊢
      have hMin : min (Int.toNat (native_seq_indexof ys pat 0)) ys.length =
          Int.toNat (native_seq_indexof ys pat 0) := by omega
      rw [hMin]
      -- expand `(k' + 1) * d = k' * d + d` and finish linearly
      have hExpand :
          (((occEnds pat
                (ys.drop
                  (Int.toNat (native_seq_indexof ys pat 0) +
                    pat.length))).length + 1 : Nat) : Int) *
              ((repl.length : Int) - (pat.length : Int)) =
            ((occEnds pat
                (ys.drop
                  (Int.toNat (native_seq_indexof ys pat 0) +
                    pat.length))).length : Int) *
                ((repl.length : Int) - (pat.length : Int)) +
              ((repl.length : Int) - (pat.length : Int)) := by
        rw [Int.natCast_add, Int.add_mul]
        simp
      rw [hExpand]
      omega

theorem replace_all_length_eq_of_same_len
    (pat repl xs : List SmtValue) (hLen : pat.length = repl.length) :
    (native_seq_replace_all xs pat repl).length = xs.length := by
  cases pat with
  | nil =>
      rw [replace_all_nil_pat]
  | cons p ps =>
      have hInt := replace_all_length_int (p :: ps) repl xs (by simp)
      have hDelta : (repl.length : Int) - ((p :: ps).length : Int) = 0 := by
        omega
      rw [hDelta] at hInt
      simp at hInt
      exact_mod_cast hInt

/-- The value of the `@strings_num_occur` skolem: the length difference of
two `replace_all`s counts the scan occurrences. -/
theorem num_occur_int (pat ys : List SmtValue) (hPat : pat ≠ []) :
    ((native_seq_replace_all ys pat (ys.take 1)).length : Int) -
      ((native_seq_replace_all ys pat []).length : Int) =
      ((occEnds pat ys).length : Int) := by
  have hPatPos : 0 < pat.length := by
    cases pat with
    | nil => exact absurd rfl hPat
    | cons => simp
  cases ys with
  | nil =>
      have hIdxNil : native_seq_indexof [] pat 0 < 0 := by
        rcases native_seq_indexof_eq_neg_one_or_ge [] pat 0 with hEq | hGe
        · rw [hEq]
          decide
        · exfalso
          have hB :=
            StrEqReplSupport.native_seq_indexof_zero_bounds_of_nonneg
              [] pat hGe
          simp only [List.length_nil] at hB
          omega
      rw [replace_all_eq_self_of_indexof_neg pat _ [] hIdxNil,
        replace_all_eq_self_of_indexof_neg pat _ [] hIdxNil,
        occEnds_eq_nil_of_indexof_neg pat [] hIdxNil]
      rfl
  | cons y ys' =>
      rw [replace_all_length_int pat ((y :: ys').take 1) (y :: ys') hPat,
        replace_all_length_int pat [] (y :: ys') hPat]
      have hTakeLen : (((y :: ys').take 1).length : Int) = 1 := by
        simp
      rw [hTakeLen]
      have hNilLen : (([] : List SmtValue).length : Int) = 0 := rfl
      rw [hNilLen]
      have hK := ((occEnds pat (y :: ys')).length : Int)
      -- k * (1 - p) - k * (0 - p) = k
      have hExpand₁ :
          ((occEnds pat (y :: ys')).length : Int) *
              (1 - (pat.length : Int)) =
            ((occEnds pat (y :: ys')).length : Int) -
              ((occEnds pat (y :: ys')).length : Int) *
                (pat.length : Int) := by
        rw [Int.mul_sub, Int.mul_one]
      have hExpand₂ :
          ((occEnds pat (y :: ys')).length : Int) *
              (0 - (pat.length : Int)) =
            0 - ((occEnds pat (y :: ys')).length : Int) *
                (pat.length : Int) := by
        rw [Int.mul_sub, Int.mul_zero]
      rw [hExpand₁, hExpand₂]
      omega

/-! ## `indexof` at an offset -/

theorem indexof_add_offset (xs pat : List SmtValue) (off w : Nat)
    (hOff : off ≤ xs.length) :
    native_seq_indexof xs pat ((off + w : Nat) : Int) =
      if native_seq_indexof (xs.drop off) pat ((w : Nat) : Int) = -1 then
        (-1 : Int)
      else
        native_seq_indexof (xs.drop off) pat ((w : Nat) : Int) +
          ((off : Nat) : Int) := by
  simp only [native_seq_indexof_eq_rec]
  rw [if_neg (by omega : ¬ ((off + w : Nat) : Int) < 0)]
  rw [if_neg (by omega : ¬ ((w : Nat) : Int) < 0)]
  simp only [Int.toNat_natCast, List.length_drop]
  by_cases hFit : off + w + pat.length ≤ xs.length
  · rw [dif_pos (by omega : off + w + pat.length ≤ xs.length),
      dif_pos (by omega : w + pat.length ≤ xs.length - off)]
    have hDrop : (xs.drop off).drop w = xs.drop (off + w) := by
      rw [List.drop_drop]
    rw [hDrop]
    have hFuel : xs.length - off - (w + pat.length) + 1 =
        xs.length - (off + w + pat.length) + 1 := by omega
    rw [hFuel]
    have hBase : off + w = w + off := by omega
    rw [hBase,
      RuleProofs.native_seq_indexof_rec_offset (xs.drop (w + off)) pat w off
        (xs.length - (w + off + pat.length) + 1)]
    simp only [Int.ofNat_eq_natCast]
  · rw [dif_neg (by omega : ¬ off + w + pat.length ≤ xs.length),
      dif_neg (by omega : ¬ w + pat.length ≤ xs.length - off)]
    rw [if_pos rfl]

/-! ## Facts at the scan boundaries -/

theorem occEnds_length_step (pat xs : List SmtValue) (hPat : pat ≠ [])
    (h : 0 ≤ native_seq_indexof xs pat 0) :
    (occEnds pat xs).length =
      (occEnds pat
          (xs.drop
            (Int.toNat (native_seq_indexof xs pat 0) +
              pat.length))).length + 1 := by
  rw [occEnds_step pat xs hPat h]
  simp [List.length_map]

theorem bound_drop_shift (pat xs : List SmtValue) (hPat : pat ≠ [])
    (h : 0 ≤ native_seq_indexof xs pat 0) (n : Nat)
    (hn : n ≤ (occEnds pat
        (xs.drop
          (Int.toNat (native_seq_indexof xs pat 0) + pat.length))).length) :
    bound pat xs (n + 1) =
      (Int.toNat (native_seq_indexof xs pat 0) + pat.length) +
        bound pat
          (xs.drop (Int.toNat (native_seq_indexof xs pat 0) + pat.length))
          n := by
  rw [bound_succ, occEnds_step pat xs hPat h]
  cases n with
  | zero =>
      simp [bound_zero]
  | succ n =>
      simp only [List.getD_cons_succ, bound_succ]
      rw [getD_map_add _ _ n (by omega)]
      omega

theorem indexof_at_bound (pat xs : List SmtValue) (hPat : pat ≠ []) :
    ∀ n : Nat, n < (occEnds pat xs).length ->
      pat.length ≤ bound pat xs (n + 1) ∧
      bound pat xs n + pat.length ≤ bound pat xs (n + 1) ∧
      native_seq_indexof xs pat ((bound pat xs n : Nat) : Int) =
        ((bound pat xs (n + 1) - pat.length : Nat) : Int) := by
  suffices hGen : ∀ (len : Nat) (ys : List SmtValue), ys.length = len ->
      ∀ n : Nat, n < (occEnds pat ys).length ->
        pat.length ≤ bound pat ys (n + 1) ∧
        bound pat ys n + pat.length ≤ bound pat ys (n + 1) ∧
        native_seq_indexof ys pat ((bound pat ys n : Nat) : Int) =
          ((bound pat ys (n + 1) - pat.length : Nat) : Int) by
    exact hGen xs.length xs rfl
  intro len
  induction len using Nat.strongRecOn with
  | ind len ih =>
      intro ys hLen n hn
      have hPatPos : 0 < pat.length := by
        cases pat with
        | nil => exact absurd rfl hPat
        | cons => simp
      have hNonneg : 0 ≤ native_seq_indexof ys pat 0 := by
        by_cases hNeg : native_seq_indexof ys pat 0 < 0
        · rw [occEnds_eq_nil_of_indexof_neg pat ys hNeg] at hn
          simp at hn
        · exact int_nonneg_of_not_neg hNeg
      have hBounds :=
        StrEqReplSupport.native_seq_indexof_zero_bounds_of_nonneg
          ys pat hNonneg
      have hE0 : bound pat ys 1 =
          Int.toNat (native_seq_indexof ys pat 0) + pat.length := by
        rw [bound_succ, occEnds_step pat ys hPat hNonneg]
        simp
      cases n with
      | zero =>
          refine ⟨?_, ?_, ?_⟩
          · rw [hE0]; omega
          · rw [bound_zero, hE0]; omega
          · rw [bound_zero, hE0]
            have hSub :
                Int.toNat (native_seq_indexof ys pat 0) + pat.length -
                    pat.length =
                  Int.toNat (native_seq_indexof ys pat 0) := by omega
            rw [hSub]
            have hCast :
                ((Int.toNat (native_seq_indexof ys pat 0) : Nat) : Int) =
                  native_seq_indexof ys pat 0 :=
              Int.toNat_of_nonneg hNonneg
            rw [hCast]
            norm_cast
      | succ n =>
          have hkStep := occEnds_length_step pat ys hPat hNonneg
          have hnDrop : n <
              (occEnds pat
                (ys.drop
                  (Int.toNat (native_seq_indexof ys pat 0) +
                    pat.length))).length := by omega
          have hDropLt :
              (ys.drop
                  (Int.toNat (native_seq_indexof ys pat 0) +
                    pat.length)).length < len := by
            rw [List.length_drop]; omega
          have hIH := ih _ hDropLt
            (ys.drop
              (Int.toNat (native_seq_indexof ys pat 0) + pat.length))
            rfl n hnDrop
          have hShift₁ := bound_drop_shift pat ys hPat hNonneg n
            (by omega)
          have hShift₂ := bound_drop_shift pat ys hPat hNonneg (n + 1)
            (by omega)
          refine ⟨?_, ?_, ?_⟩
          · rw [hShift₂]
            have := hIH.1
            omega
          · rw [hShift₁, hShift₂]
            have := hIH.2.1
            omega
          · rw [hShift₁, hShift₂]
            have hOffLe :
                Int.toNat (native_seq_indexof ys pat 0) + pat.length ≤
                  ys.length := hBounds
            have hOffset := indexof_add_offset ys pat
              (Int.toNat (native_seq_indexof ys pat 0) + pat.length)
              (bound pat
                (ys.drop
                  (Int.toNat (native_seq_indexof ys pat 0) + pat.length))
                n)
              hOffLe
            rw [hOffset, hIH.2.2]
            rw [if_neg (by
              have := hIH.1
              have h1 := hIH.2.1
              intro hAbs
              unfold native_Int at *
              omega)]
            have := hIH.1
            have h1 := hIH.2.1
            unfold native_Int at *
            push_cast
            omega

theorem indexof_at_bound_last (pat xs : List SmtValue) (hPat : pat ≠ []) :
    native_seq_indexof xs pat
        ((bound pat xs (occEnds pat xs).length : Nat) : Int) = -1 := by
  suffices hGen : ∀ (len : Nat) (ys : List SmtValue), ys.length = len ->
      native_seq_indexof ys pat
          ((bound pat ys (occEnds pat ys).length : Nat) : Int) = -1 by
    exact hGen xs.length xs rfl
  intro len
  induction len using Nat.strongRecOn with
  | ind len ih =>
      intro ys hLen
      have hPatPos : 0 < pat.length := by
        cases pat with
        | nil => exact absurd rfl hPat
        | cons => simp
      by_cases hNeg : native_seq_indexof ys pat 0 < 0
      · rw [occEnds_eq_nil_of_indexof_neg pat ys hNeg]
        simp only [List.length_nil, bound_zero, Int.natCast_zero]
        rcases native_seq_indexof_eq_neg_one_or_ge ys pat 0 with hEq | hGe
        · exact hEq
        · exfalso
          unfold native_Int at *
          omega
      have hNonneg : 0 ≤ native_seq_indexof ys pat 0 :=
        int_nonneg_of_not_neg hNeg
      have hBounds :=
        StrEqReplSupport.native_seq_indexof_zero_bounds_of_nonneg
          ys pat hNonneg
      have hkStep := occEnds_length_step pat ys hPat hNonneg
      rw [hkStep]
      rw [bound_drop_shift pat ys hPat hNonneg _ (by omega)]
      have hDropLt :
          (ys.drop
              (Int.toNat (native_seq_indexof ys pat 0) +
                pat.length)).length < len := by
        rw [List.length_drop]; omega
      have hIH := ih _ hDropLt
        (ys.drop (Int.toNat (native_seq_indexof ys pat 0) + pat.length))
        rfl
      have hOffset := indexof_add_offset ys pat
        (Int.toNat (native_seq_indexof ys pat 0) + pat.length)
        (bound pat
          (ys.drop
            (Int.toNat (native_seq_indexof ys pat 0) + pat.length))
          (occEnds pat
            (ys.drop
              (Int.toNat (native_seq_indexof ys pat 0) +
                pat.length))).length)
        hBounds
      rw [hOffset, hIH, if_pos rfl]

/-! ## `indexof` / `replace_all` on suffixes at the boundaries -/

theorem indexof_drop_bound (pat xs : List SmtValue) (hPat : pat ≠ [])
    (n : Nat) (hn : n < (occEnds pat xs).length) :
    native_seq_indexof (xs.drop (bound pat xs n)) pat 0 =
      (((bound pat xs (n + 1) - pat.length) - bound pat xs n : Nat) :
        Int) := by
  rcases indexof_at_bound pat xs hPat n hn with ⟨hPatLe, hMono, hIdx⟩
  have hBLe : bound pat xs n ≤ xs.length :=
    bound_le_len pat xs n (by omega)
  have hOffset := indexof_add_offset xs pat (bound pat xs n) 0 hBLe
  rw [Nat.add_zero] at hOffset
  rw [hOffset] at hIdx
  have hZeroCast : (((0 : Nat) : Int)) = (0 : Int) := by norm_cast
  rw [hZeroCast] at hIdx
  by_cases hInner :
      native_seq_indexof (xs.drop (bound pat xs n)) pat 0 = -1
  · rw [if_pos hInner] at hIdx
    exfalso
    unfold native_Int at *
    omega
  · rw [if_neg hInner] at hIdx
    rcases native_seq_indexof_eq_neg_one_or_ge
        (xs.drop (bound pat xs n)) pat 0 with hEq | hGe
    · exact absurd hEq hInner
    · unfold native_Int at *
      push_cast at hIdx ⊢
      omega

theorem indexof_drop_bound_last (pat xs : List SmtValue) (hPat : pat ≠ []) :
    native_seq_indexof (xs.drop (bound pat xs (occEnds pat xs).length))
        pat 0 = -1 := by
  have hLast := indexof_at_bound_last pat xs hPat
  have hBLe : bound pat xs (occEnds pat xs).length ≤ xs.length :=
    bound_le_len pat xs _ (by omega)
  have hOffset := indexof_add_offset xs pat
    (bound pat xs (occEnds pat xs).length) 0 hBLe
  rw [Nat.add_zero] at hOffset
  rw [hOffset] at hLast
  have hZeroCast : (((0 : Nat) : Int)) = (0 : Int) := by norm_cast
  rw [hZeroCast] at hLast
  by_cases hInner :
      native_seq_indexof
          (xs.drop (bound pat xs (occEnds pat xs).length)) pat 0 = -1
  · exact hInner
  · rw [if_neg hInner] at hLast
    exfalso
    rcases native_seq_indexof_eq_neg_one_or_ge
        (xs.drop (bound pat xs (occEnds pat xs).length)) pat 0 with
      hEq | hGe
    · exact hInner hEq
    · unfold native_Int at *
      omega

theorem replace_all_drop_bound_last (pat repl xs : List SmtValue)
    (hPat : pat ≠ []) :
    native_seq_replace_all
        (xs.drop (bound pat xs (occEnds pat xs).length)) pat repl =
      xs.drop (bound pat xs (occEnds pat xs).length) := by
  apply replace_all_eq_self_of_indexof_neg
  rw [indexof_drop_bound_last pat xs hPat]
  decide

theorem replace_all_drop_bound_step (pat repl xs : List SmtValue)
    (hPat : pat ≠ []) (n : Nat) (hn : n < (occEnds pat xs).length) :
    native_seq_replace_all (xs.drop (bound pat xs n)) pat repl =
      (xs.drop (bound pat xs n)).take
          ((bound pat xs (n + 1) - pat.length) - bound pat xs n) ++
        repl ++
        native_seq_replace_all (xs.drop (bound pat xs (n + 1))) pat
          repl := by
  rcases indexof_at_bound pat xs hPat n hn with ⟨hPatLe, hMono, _⟩
  have hIdxDrop := indexof_drop_bound pat xs hPat n hn
  have hNonneg : 0 ≤ native_seq_indexof (xs.drop (bound pat xs n)) pat 0 := by
    rw [hIdxDrop]
    exact Int.natCast_nonneg _
  rw [replace_all_step pat repl _ hPat hNonneg]
  rw [hIdxDrop]
  have hToNat :
      Int.toNat
          ((((bound pat xs (n + 1) - pat.length) - bound pat xs n : Nat) :
            Int)) =
        (bound pat xs (n + 1) - pat.length) - bound pat xs n := by
    simp
  rw [hToNat]
  have hDropDrop :
      (xs.drop (bound pat xs n)).drop
          ((bound pat xs (n + 1) - pat.length) - bound pat xs n +
            pat.length) =
        xs.drop (bound pat xs (n + 1)) := by
    rw [List.drop_drop]
    congr 1
    omega
  rw [hDropDrop]
