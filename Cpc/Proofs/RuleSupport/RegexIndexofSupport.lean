module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

public section

open Eo
open SmtEval
open Smtm

set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

namespace StringReductionRegex

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

private theorem valid_take (xs : native_String) (n : Nat)
    (h : native_string_valid xs = true) :
    native_string_valid (xs.take n) = true := by
  simp [native_string_valid] at h ⊢
  intro c hc
  exact h c (List.mem_of_mem_take hc)

private theorem in_re_cons
    (c : native_Char) (cs : native_String) (r : SmtRegLan)
    (hValid : native_string_valid (c :: cs) = true) :
    native_str_in_re (c :: cs) r =
      native_str_in_re cs (native_re_deriv c r) := by
  have hTail : native_string_valid cs = true := by
    simpa [native_string_valid, Bool.and_eq_true] using
      (show native_char_valid c = true ∧ native_string_valid cs = true by
        simpa [native_string_valid, Bool.and_eq_true] using hValid).2
  have hValueValid :
      native_re_str_valid (impl_native_string_to_values (c :: cs)) = true := by
    rw [native_re_str_valid_string]
    exact hValid
  have hTailValueValid :
      native_re_str_valid (impl_native_string_to_values cs) = true := by
    rw [native_re_str_valid_string]
    exact hTail
  simp only [impl_native_string_to_values, List.map_cons] at hValueValid hTailValueValid
  simp only [impl_native_string_to_values, List.map_cons]
  simp [Smtm.native_str_in_re, hValueValid, hTailValueValid]

private theorem prefix_go_some_spec (r : SmtRegLan) :
    ∀ (xs : native_String) (n found : Nat),
      native_string_valid xs = true →
      impl_native_re_prefix_match_len_go r xs n = some found →
      n ≤ found ∧ found ≤ n + xs.length ∧
        native_str_in_re (xs.take (found - n)) r = true
  | [], n, found, hValid, hFind => by
      simp only [impl_native_string_to_values, List.map] at hFind
      rw [impl_native_re_prefix_match_len_go.eq_1] at hFind
      split at hFind
      · cases hFind
        simp [native_str_in_re, native_re_str_valid, native_string_valid, *]
      · simp at hFind
  | c :: cs, n, found, hValid, hFind => by
      have hParts : native_char_valid c = true ∧
          native_string_valid cs = true := by
        simpa [native_string_valid] using hValid
      simp only [impl_native_string_to_values, List.map] at hFind
      rw [impl_native_re_prefix_match_len_go.eq_2] at hFind
      split at hFind
      · cases hFind
        simp [native_str_in_re, native_re_str_valid, native_string_valid, *]
      ·
        have ih := prefix_go_some_spec (native_re_deriv c r) cs (n + 1)
          found hParts.2 hFind
        rcases ih with ⟨hLo, hHi, hMatch⟩
        have hPos : n < found := by omega
        have hTake :
            (c :: cs).take (found - n) =
              c :: cs.take (found - (n + 1)) := by
          cases hDiff : found - n with
          | zero => omega
          | succ k =>
              have hk : k = found - (n + 1) := by omega
              simp [hDiff, hk]
        refine ⟨by omega, by simp only [List.length_cons]; omega, ?_⟩
        have hTakeValues := congrArg (List.map SmtValue.Char) hTake
        simp only [List.map_take, List.map_cons] at hTakeValues
        simp only [impl_native_string_to_values, List.map_cons] at hMatch ⊢
        rw [hTakeValues]
        have hCons := in_re_cons c (cs.take (found - (n + 1))) r
        simp only [impl_native_string_to_values, List.map_take] at hCons
        rw [hCons]
        · exact hMatch
        · have hTakeValid := valid_take cs (found - (n + 1)) hParts.2
          simpa [native_string_valid, Bool.and_eq_true] using
            And.intro hParts.1 hTakeValid

private theorem prefix_go_none_spec (r : SmtRegLan) :
    ∀ (xs : native_String) (n : Nat),
      native_string_valid xs = true →
      impl_native_re_prefix_match_len_go r xs n = none →
      ∀ k, k ≤ xs.length →
        native_str_in_re (xs.take k) r = false
  | [], n, hValid, hFind, k, hk => by
      have hk0 : k = 0 := by simpa using hk
      subst k
      simp only [impl_native_string_to_values, List.map] at hFind
      rw [impl_native_re_prefix_match_len_go.eq_1] at hFind
      split at hFind
      · simp at hFind
      · rename_i hNull
        simpa [native_str_in_re, native_re_str_valid, native_string_valid] using hNull
  | c :: cs, n, hValid, hFind, k, hk => by
      have hParts : native_char_valid c = true ∧
          native_string_valid cs = true := by
        simpa [native_string_valid] using hValid
      simp only [impl_native_string_to_values, List.map] at hFind
      rw [impl_native_re_prefix_match_len_go.eq_2] at hFind
      split at hFind
      · simp at hFind
      · rename_i hNull
        cases k with
        | zero =>
            simpa [native_str_in_re, native_re_str_valid,
              native_string_valid] using hNull
        | succ k =>
            have hk' : k ≤ cs.length := by
              simp only [List.length_cons] at hk
              omega
            simp only [impl_native_string_to_values, List.map_cons]
            rw [List.take_succ_cons]
            have hCons := in_re_cons c (cs.take k) r
            simp only [impl_native_string_to_values, List.map_take] at hCons
            rw [hCons]
            · exact prefix_go_none_spec (native_re_deriv c r) cs (n + 1)
                hParts.2 hFind k hk'
            · have hTakeValid := valid_take cs k hParts.2
              simpa [native_string_valid, Bool.and_eq_true] using
                And.intro hParts.1 hTakeValid

private theorem prefix_some_spec
    (r : SmtRegLan) (xs : native_String) (found : Nat)
    (hValid : native_string_valid xs = true)
    (hFind : native_re_prefix_match_len? r xs = some found) :
    found ≤ xs.length ∧
      native_str_in_re (xs.take found) r = true := by
  have h := prefix_go_some_spec r xs 0 found hValid (by
    simpa [native_re_prefix_match_len?] using hFind)
  have hBound : found ≤ xs.length := by simpa using h.2.1
  have hMatch : native_str_in_re (xs.take found) r = true := by
    simpa using h.2.2
  exact ⟨hBound, hMatch⟩

private theorem prefix_none_spec
    (r : SmtRegLan) (xs : native_String)
    (hValid : native_string_valid xs = true)
    (hFind : native_re_prefix_match_len? r xs = none) :
    ∀ k, k ≤ xs.length →
      native_str_in_re (xs.take k) r = false := by
  exact prefix_go_none_spec r xs 0 hValid (by
    simpa [native_re_prefix_match_len?] using hFind)

private theorem valid_drop (xs : native_String) (n : Nat)
    (h : native_string_valid xs = true) :
    native_string_valid (xs.drop n) = true := by
  simp [native_string_valid] at h ⊢
  intro c hc
  exact h c (List.mem_of_mem_drop hc)

private theorem find_some_spec (r : SmtRegLan) :
    ∀ (xs : native_String) (idx found len : Nat),
      native_string_valid xs = true →
      impl_native_re_find_idx_aux r xs idx = some (found, len) →
      idx ≤ found ∧ found ≤ idx + xs.length ∧
        len ≤ (xs.drop (found - idx)).length ∧
        native_str_in_re ((xs.drop (found - idx)).take len) r = true ∧
        ∀ j, idx ≤ j → j < found →
          ∀ k, k ≤ (xs.drop (j - idx)).length →
            native_str_in_re ((xs.drop (j - idx)).take k) r = false
  | [], idx, found, len, hValid, hFind => by
      simp only [impl_native_string_to_values, List.map] at hFind
      rw [impl_native_re_find_idx_aux.eq_def] at hFind
      cases hPref : native_re_prefix_match_len? r [] with
      | none => simp [hPref] at hFind
      | some n =>
          simp [hPref] at hFind
          obtain ⟨rfl, rfl⟩ := hFind
          have hSpec := prefix_some_spec r [] n hValid hPref
          have hn : n = 0 := by simpa using hSpec.1
          subst n
          refine ⟨by simp, by simp, by simp, by simpa using hSpec.2, ?_⟩
          intro j hj hlt
          omega
  | c :: cs, idx, found, len, hValid, hFind => by
      have hParts : native_char_valid c = true ∧
          native_string_valid cs = true := by
        simpa [native_string_valid] using hValid
      simp only [impl_native_string_to_values, List.map] at hFind
      rw [impl_native_re_find_idx_aux.eq_def] at hFind
      cases hPref : native_re_prefix_match_len? r (c :: cs) with
      | some n =>
          simp only [impl_native_string_to_values] at hPref
          simp [hPref] at hFind
          obtain ⟨rfl, rfl⟩ := hFind
          have hSpec := prefix_some_spec r (c :: cs) n hValid hPref
          refine ⟨by simp, by simp, ?_, ?_, ?_⟩
          · simpa using hSpec.1
          · simpa using hSpec.2
          · intro j hj hlt
            omega
      | none =>
          simp only [impl_native_string_to_values] at hPref
          simp [hPref] at hFind
          have ih := find_some_spec r cs (idx + 1) found len hParts.2 hFind
          rcases ih with ⟨hLo, hHi, hLen, hMatch, hMin⟩
          have hFoundPos : idx < found := by omega
          have hDropFound :
              (c :: cs).drop (found - idx) =
                cs.drop (found - (idx + 1)) := by
            have hSub : found - idx = (found - (idx + 1)) + 1 := by omega
            rw [hSub]
            simp
          refine ⟨by omega, ?_, ?_, ?_, ?_⟩
          · simp only [List.length_cons]
            omega
          · simpa [hDropFound] using hLen
          · simpa [hDropFound] using hMatch
          · intro j hjLo hjHi k hk
            by_cases hjEq : j = idx
            · subst j
              simpa using prefix_none_spec r (c :: cs) hValid hPref k (by
                simpa using hk)
            · have hjNext : idx + 1 ≤ j := by omega
              have hDropJ :
                  (c :: cs).drop (j - idx) =
                    cs.drop (j - (idx + 1)) := by
                have hSub : j - idx = (j - (idx + 1)) + 1 := by omega
                rw [hSub]
                simp
              simpa [hDropJ] using hMin j hjNext hjHi k (by
                simpa [hDropJ] using hk)

private theorem find_none_spec (r : SmtRegLan) :
    ∀ (xs : native_String) (idx : Nat),
      native_string_valid xs = true →
      impl_native_re_find_idx_aux r xs idx = none →
      ∀ j, idx ≤ j → j ≤ idx + xs.length →
        ∀ k, k ≤ (xs.drop (j - idx)).length →
          native_str_in_re ((xs.drop (j - idx)).take k) r = false
  | [], idx, hValid, hFind, j, hjLo, hjHi, k, hk => by
      simp only [List.length_nil, Nat.add_zero] at hjHi
      have hjEq : j = idx := by omega
      subst j
      simp only [impl_native_string_to_values, List.map] at hFind
      rw [impl_native_re_find_idx_aux.eq_def] at hFind
      cases hPref : native_re_prefix_match_len? r [] with
      | some n => simp [hPref] at hFind
      | none =>
          simpa only [Nat.sub_self, List.drop_zero] using
            prefix_none_spec r [] hValid hPref k (by simpa using hk)
  | c :: cs, idx, hValid, hFind, j, hjLo, hjHi, k, hk => by
      have hParts : native_char_valid c = true ∧
          native_string_valid cs = true := by
        simpa [native_string_valid] using hValid
      simp only [impl_native_string_to_values, List.map] at hFind
      rw [impl_native_re_find_idx_aux.eq_def] at hFind
      cases hPref : native_re_prefix_match_len? r (c :: cs) with
      | some n =>
          simp only [impl_native_string_to_values] at hPref
          simp [hPref] at hFind
      | none =>
          simp only [impl_native_string_to_values] at hPref
          simp [hPref] at hFind
          by_cases hjEq : j = idx
          · subst j
            simpa only [Nat.sub_self, List.drop_zero] using
              prefix_none_spec r (c :: cs) hValid hPref k (by
                simpa using hk)
          · have hjNext : idx + 1 ≤ j := by omega
            have hjHi' : j ≤ idx + 1 + cs.length := by
              simp only [List.length_cons] at hjHi
              omega
            have hDropJ :
                (c :: cs).drop (j - idx) =
                  cs.drop (j - (idx + 1)) := by
              have hSub : j - idx = (j - (idx + 1)) + 1 := by omega
              rw [hSub]
              simp
            rw [hDropJ]
            exact find_none_spec r cs (idx + 1) hParts.2 hFind j hjNext
              hjHi' k (by simpa [hDropJ] using hk)

private theorem substr_of_nat_bounds
    (s : native_String) (j k : Nat)
    (hj : j < s.length) (hkPos : 0 < k)
    (hk : k ≤ s.length - j) :
    native_str_substr s (j : Int) (k : Int) =
      (s.drop j).take k := by
  have hStartNotNeg : ¬ (j : Int) < 0 :=
    Int.not_lt.mpr (Int.natCast_nonneg j)
  have hLenNotNonpos : ¬ (k : Int) ≤ 0 := by omega
  have hStartNotHigh : ¬ (s.length : Int) ≤ (j : Int) := by omega
  have hMin :
      min (k : Int) ((s.length : Int) - (j : Int)) = (k : Int) := by
    apply Int.min_eq_left
    omega
  have hkZero : k ≠ 0 := Nat.ne_of_gt hkPos
  have hjHigh : ¬ s.length ≤ j := Nat.not_le_of_lt hj
  simp [native_str_substr, native_str_len, hStartNotNeg, hkZero, hjHigh,
    hMin]

private theorem natCast_eq_ofNat (j : Nat) :
    (j : Int) = Int.ofNat j := by
  cases j <;> rfl

private theorem substr_of_ofNat_bounds
    (s : native_String) (j k : Nat)
    (hj : j < s.length) (hkPos : 0 < k)
    (hk : k ≤ s.length - j) :
    native_str_substr s (Int.ofNat j) (Int.ofNat k) =
      (s.drop j).take k := by
  rw [← natCast_eq_ofNat j, ← natCast_eq_ofNat k]
  exact substr_of_nat_bounds s j k hj hkPos hk

private theorem drop_drop_from_start
    (s : native_String) (start found : Nat)
    (hStart : start ≤ found) :
    (s.drop start).drop (found - start) = s.drop found := by
  rw [List.drop_drop]
  congr
  omega

theorem search_semantics
    (s : native_String) (r : SmtRegLan) (start : Nat)
    (hValid : native_string_valid s = true)
    (hStart : start ≤ s.length)
    (hEmpty : native_str_in_re [] r = false) :
    let result := native_str_indexof_re s r (Int.ofNat start)
    (∀ j, start ≤ j →
        j < (if result = -1 then s.length else Int.toNat result) →
        ∀ k, 0 < k → k ≤ s.length - j →
          native_str_in_re (native_str_substr s (Int.ofNat j) (Int.ofNat k)) r =
            false) ∧
      (result = -1 ∨
        (Int.ofNat start ≤ result ∧
          ∃ k, 0 < k ∧ k ≤ s.length - Int.toNat result ∧
            native_str_in_re
              (native_str_substr s result (Int.ofNat k)) r = true)) := by
  dsimp
  have hStartInt : ¬ (start : Int) < 0 :=
    Int.not_lt.mpr (Int.natCast_nonneg start)
  have hToNat : (start : Int).toNat = start := rfl
  have hDropValid := valid_drop s start hValid
  have hDropLen : (s.drop start).length = s.length - start := by simp
  have hResult :
      native_str_indexof_re s r (start : Int) =
        match native_re_find_idx_from r s start with
        | some (idx, _) => Int.ofNat idx
        | none => -1 := by
    have hStartValues : start ≤ (impl_native_string_to_values s).length := by
      simpa [impl_native_string_to_values] using hStart
    simp [native_str_indexof_re, hStartInt, hToNat, hStartValues]
    rfl
  simp only [hResult]
  cases hFind : native_re_find_idx_from r s start with
  | none =>
      have hAux :
          impl_native_re_find_idx_aux r (impl_native_string_to_values (s.drop start)) start =
            none := by
        simpa [native_re_find_idx_from, impl_native_string_to_values,
          List.map_drop] using hFind
      have hNone := find_none_spec r (s.drop start) start hDropValid hAux
      constructor
      · intro j hjLo hjHi k hkPos hk
        have hjLe : j ≤ start + (s.drop start).length := by
          simp [List.length_drop]
          omega
        have hNo := hNone j hjLo hjLe k (by
          simp [List.length_drop]
          omega)
        rw [drop_drop_from_start s start j hjLo] at hNo
        rw [substr_of_nat_bounds s j k (by omega) hkPos hk]
        simpa [impl_native_string_to_values, List.map_take] using hNo
      · exact Or.inl rfl
  | some p =>
      rcases p with ⟨found, len⟩
      have hAux :
          impl_native_re_find_idx_aux r (impl_native_string_to_values (s.drop start)) start =
            some (found, len) := by
        simpa [native_re_find_idx_from, impl_native_string_to_values,
          List.map_drop] using hFind
      have hSome := find_some_spec r (s.drop start) start found len
        hDropValid hAux
      rcases hSome with ⟨hLo, hHi, hLen, hMatch, hMin⟩
      have hFoundLe : found ≤ s.length := by
        simp [List.length_drop] at hHi
        omega
      have hDropFound :
          (s.drop start).drop (found - start) = s.drop found :=
        drop_drop_from_start s start found hLo
      rw [hDropFound] at hLen hMatch
      have hLenPos : 0 < len := by
        apply Nat.pos_of_ne_zero
        intro hZero
        subst len
        simp at hMatch
        rw [hEmpty] at hMatch
        contradiction
      have hFoundLt : found < s.length := by
        simp [List.length_drop] at hLen
        omega
      constructor
      · intro j hjLo hjHi k hkPos hk
        have hjFound : j < found := by simpa using hjHi
        have hNo := hMin j hjLo hjFound k (by
          rw [drop_drop_from_start s start j hjLo]
          simp [List.length_drop]
          exact hk)
        rw [drop_drop_from_start s start j hjLo] at hNo
        rw [substr_of_nat_bounds s j k (by omega) hkPos hk]
        simpa [impl_native_string_to_values, List.map_take] using hNo
      · right
        refine ⟨by exact Int.ofNat_le.mpr hLo, len, hLenPos, ?_, ?_⟩
        · simpa [List.length_drop] using hLen
        · simp only [hFind]
          rw [natCast_eq_ofNat len]
          rw [substr_of_ofNat_bounds s found len hFoundLt hLenPos (by
            simpa [List.length_drop] using hLen)]
          simpa [impl_native_string_to_values, List.map_take] using hMatch

private theorem prefix_match_zero_of_nullable
    (r : SmtRegLan) (xs : native_String)
    (h : native_re_nullable r = true) :
    native_re_prefix_match_len? r xs = some 0 := by
  rw [native_re_prefix_match_len?.eq_1]
  cases xs with
  | nil =>
      simp only [impl_native_string_to_values, List.map]
      simp [impl_native_re_prefix_match_len_go.eq_1, h]
  | cons c cs =>
      simp only [impl_native_string_to_values, List.map]
      simp [impl_native_re_prefix_match_len_go.eq_2, h]

private theorem find_at_start_of_nullable
    (r : SmtRegLan) (xs : native_String) (start : Nat)
    (h : native_re_nullable r = true) :
    native_re_find_idx_from r xs start = some (start, 0) := by
  unfold native_re_find_idx_from
  rw [impl_native_re_find_idx_aux.eq_def]
  have hPref := prefix_match_zero_of_nullable r (xs.drop start) h
  simp only [impl_native_string_to_values, List.map_drop] at hPref ⊢
  rw [hPref]

theorem search_eq_start_of_empty_match
    (s : native_String) (r : SmtRegLan) (start : Nat)
    (_hValid : native_string_valid s = true)
    (hStart : start ≤ s.length)
    (hEmpty : native_str_in_re [] r = true) :
    native_str_indexof_re s r (Int.ofNat start) = Int.ofNat start := by
  have hNullable : native_re_nullable r = true := by
    have hParts : native_re_str_valid [] = true ∧ native_re_nullable r = true := by
      simpa [Smtm.native_str_in_re] using hEmpty
    exact hParts.2
  have hFind := find_at_start_of_nullable r s start hNullable
  have hStartValues : start ≤ (impl_native_string_to_values s).length := by
    simpa [impl_native_string_to_values] using hStart
  simp [native_str_indexof_re, hStartValues, hFind]

theorem search_eq_neg_one_of_invalid
    (s : native_String) (r : SmtRegLan) (start : Int)
    (hInvalid : start > (s.length : Int) ∨ 0 > start) :
    native_str_indexof_re s r start = -1 := by
  by_cases hNeg : start < 0
  · simp [native_str_indexof_re, hNeg]
  · have hHigh : (s.length : Int) < start := by omega
    have hToNatHigh : s.length < start.toNat := by
      apply Int.ofNat_lt.mp
      simpa [Int.toNat_of_nonneg (Int.le_of_not_gt hNeg)] using hHigh
    have hToNatHighValues : (impl_native_string_to_values s).length < start.toNat := by
      simpa [impl_native_string_to_values] using hToNatHigh
    simp [native_str_indexof_re, hNeg, Nat.not_le_of_lt hToNatHighValues]

/-- Integer-valued form of regex search semantics, matching the arithmetic
shape used by the generated string-reduction predicate. -/
theorem search_semantics_int
    (s : native_String) (r : SmtRegLan) (start : Int)
    (hValid : native_string_valid s = true) :
    let result := native_str_indexof_re s r start
    if start > (s.length : Int) ∨ 0 > start then
      result = -1
    else if native_str_in_re [] r then
      result = start
    else
      (forall j k : Int,
        ¬ start ≤ j ∨
        ¬ j < (if result = -1 then (s.length : Int) else result) ∨
        ¬ 0 < k ∨
        ¬ k ≤ (s.length : Int) - j ∨
        native_str_in_re (native_str_substr s j k) r = false) ∧
      (result = -1 ∨
        (start ≤ result ∧
          exists k : Int, 0 ≤ k ∧
            k ≤ (s.length : Int) - result ∧
            native_str_in_re (native_str_substr s result k) r = true)) := by
  dsimp
  by_cases hInvalid : start > (s.length : Int) ∨ 0 > start
  · rw [if_pos hInvalid]
    exact search_eq_neg_one_of_invalid s r start hInvalid
  · rw [if_neg hInvalid]
    have hStartNonneg : 0 ≤ start := by omega
    have hStartHigh : start ≤ (s.length : Int) := by omega
    let startNat := start.toNat
    have hStartCast : Int.ofNat startNat = start := by
      simpa [startNat] using Int.toNat_of_nonneg hStartNonneg
    have hStartNat : startNat ≤ s.length := by
      omega
    by_cases hEmpty : native_str_in_re [] r = true
    · rw [if_pos hEmpty]
      rw [← hStartCast]
      exact search_eq_start_of_empty_match s r startNat hValid hStartNat hEmpty
    · have hEmptyFalse : native_str_in_re [] r = false := by
        cases hVal : native_str_in_re [] r with
        | false => rfl
        | true => exact False.elim (hEmpty hVal)
      rw [if_neg hEmpty]
      have hSem := search_semantics s r startNat hValid hStartNat hEmptyFalse
      rw [hStartCast] at hSem
      rcases hSem with ⟨hMinimal, hFound⟩
      constructor
      · intro j k
        by_cases hjLo : start ≤ j
        · by_cases hjHi :
              j < (if native_str_indexof_re s r start = -1 then
                (s.length : Int) else native_str_indexof_re s r start)
          · by_cases hkPos : 0 < k
            · by_cases hkHi : k ≤ (s.length : Int) - j
              · have hjNonneg : 0 ≤ j := by omega
                let jNat := j.toNat
                let kNat := k.toNat
                have hjCast : Int.ofNat jNat = j := by
                  simpa [jNat] using Int.toNat_of_nonneg hjNonneg
                have hkCast : Int.ofNat kNat = k := by
                  simpa [kNat] using
                    Int.toNat_of_nonneg (Int.le_of_lt hkPos)
                have hjLoNat : startNat ≤ jNat := by
                  omega
                have hjHiNat :
                    jNat <
                      (if native_str_indexof_re s r start = -1 then
                        s.length
                      else Int.toNat (native_str_indexof_re s r start)) := by
                  by_cases hResult :
                      native_str_indexof_re s r start = -1
                  · simp only [hResult, if_pos] at hjHi ⊢
                    omega
                  · simp only [hResult, if_false] at hjHi ⊢
                    have hResultNonneg :
                        0 ≤ native_str_indexof_re s r start := by
                      exact Int.le_of_lt (Int.lt_of_le_of_lt hjNonneg hjHi)
                    have hResultCast :
                        Int.ofNat
                            (Int.toNat (native_str_indexof_re s r start)) =
                          native_str_indexof_re s r start :=
                      Int.toNat_of_nonneg hResultNonneg
                    omega
                have hkPosNat : 0 < kNat := by
                  omega
                have hkHiNat : kNat ≤ s.length - jNat := by
                  omega
                have hNo := hMinimal jNat hjLoNat hjHiNat kNat hkPosNat hkHiNat
                right; right; right; right
                have hSubstr :
                    native_str_substr s (Int.ofNat jNat) (Int.ofNat kNat) =
                      native_str_substr s j k := by
                  rw [hjCast, hkCast]
                rw [hSubstr] at hNo
                exact hNo
              · right; right; right; exact Or.inl hkHi
            · right; right; exact Or.inl hkPos
          · right; exact Or.inl hjHi
        · exact Or.inl hjLo
      · rcases hFound with hNotFound | ⟨hResultLo, k, hkPos, hkHi, hMatch⟩
        · exact Or.inl hNotFound
        · right
          refine ⟨hResultLo, Int.ofNat k, Int.natCast_nonneg k, ?_, ?_⟩
          · have hResultNonneg : 0 ≤ native_str_indexof_re s r start :=
              Int.le_trans hStartNonneg hResultLo
            have hResultCast :
                Int.ofNat (Int.toNat (native_str_indexof_re s r start)) =
                  native_str_indexof_re s r start :=
              Int.toNat_of_nonneg hResultNonneg
            have hResultNatLe :
                Int.toNat (native_str_indexof_re s r start) ≤ s.length := by
              omega
            have hBound := Int.ofNat_le.mpr hkHi
            rw [Int.ofNat_sub hResultNatLe] at hBound
            calc
              Int.ofNat k = (k : Int) := (natCast_eq_ofNat k).symm
              _ ≤ (s.length : Int) -
                    (Int.toNat (native_str_indexof_re s r start) : Int) :=
                hBound
              _ = (s.length : Int) - native_str_indexof_re s r start := by
                exact congrArg (fun q : Int => (s.length : Int) - q)
                  (calc
                    (Int.toNat (native_str_indexof_re s r start) : Int) =
                        Int.ofNat
                          (Int.toNat (native_str_indexof_re s r start)) :=
                      natCast_eq_ofNat _
                    _ = native_str_indexof_re s r start := hResultCast)
          · simpa using hMatch

end StringReductionRegex
