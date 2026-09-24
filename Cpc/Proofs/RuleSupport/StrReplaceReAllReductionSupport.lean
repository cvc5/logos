module

public import Cpc.Proofs.RuleSupport.StrReplaceAllCaseSupport
import all Cpc.Proofs.RuleSupport.StrReplaceAllCaseSupport
public import Cpc.Proofs.RuleSupport.RegexIndexofSupport
import all Cpc.Proofs.RuleSupport.RegexIndexofSupport
public import Cpc.Proofs.RuleSupport.Cong.Core
import all Cpc.Proofs.RuleSupport.Cong.Core

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 40000000
set_option maxRecDepth 12000

/-!
Semantic support for the `str_replace_re_all` branch of `string_reduction`.

The generated occurrence-boundary skolem is interpreted by
`native_str_occur_index_re`, whose boundaries are the ends of successive
leftmost, shortest, nonempty regex matches.  The lemmas below connect that
scan to `native_str_replace_re_all`.
-/

namespace StrReplaceReAllReduction

@[simp] private theorem native_string_to_values_nil :
    impl_native_string_to_values [] = [] := by
  rfl

@[simp] private theorem native_string_to_values_cons
    (c : native_Char) (s : native_String) :
    impl_native_string_to_values (c :: s) =
      SmtValue.Char c :: impl_native_string_to_values s := by
  rfl

@[simp] private theorem native_string_to_values_length
    (s : native_String) :
    (impl_native_string_to_values s).length = s.length := by
  simp [impl_native_string_to_values]

@[simp] private theorem native_string_to_values_drop
    (s : native_String) (n : Nat) :
    impl_native_string_to_values (s.drop n) =
      (impl_native_string_to_values s).drop n := by
  simp [impl_native_string_to_values, List.map_drop]

@[simp] private theorem native_string_to_values_take
    (s : native_String) (n : Nat) :
    impl_native_string_to_values (s.take n) =
      (impl_native_string_to_values s).take n := by
  simp [impl_native_string_to_values, List.map_take]

/-- The regex with its empty word removed, as used by the generated
`str_replace_re_all` predicate. -/
@[expose] def nonemptyRe (r : SmtRegLan) : SmtRegLan :=
  native_re_diff r SmtRegLan.epsilon

/-- End positions of the nonempty-match scan. -/
@[expose] def reEnds (r : SmtRegLan) (s : native_String) : List Nat :=
  impl_native_re_scan_ends_aux (s.length + 1) r (impl_native_string_to_values s) 0

/-- Scan boundary zero is `0`; later boundaries are elements of `reEnds`. -/
@[expose] def reBound (r : SmtRegLan) (s : native_String) (n : Nat) : Nat :=
  (0 :: reEnds r s).getD n 0

theorem reBound_zero (r : SmtRegLan) (s : native_String) :
    reBound r s 0 = 0 := rfl

theorem reBound_succ (r : SmtRegLan) (s : native_String) (n : Nat) :
    reBound r s (n + 1) = (reEnds r s).getD n 0 := rfl

/-- Evaluation of the occurrence-boundary skolem at a natural count. -/
theorem occur_index_re_ofNat_eq_reBound
    (s : native_String) (r : SmtRegLan) (n : Nat) :
    native_str_occur_index_re (impl_native_string_to_values s) r (Int.ofNat n) =
      if n ≤ (reEnds r s).length then
        Int.ofNat (reBound r s n)
      else
        -1 := by
  simp [native_str_occur_index_re, reEnds, reBound, Nat.lt_succ_iff]

/-- Removing epsilon really makes the regex non-nullable. -/
theorem nonemptyRe_nullable_false (r : SmtRegLan) :
    native_re_nullable (nonemptyRe r) = false := by
  rw [nonemptyRe, native_re_diff, RuleProofs.native_re_nullable_mk_inter]
  have hComp :
      native_re_nullable (native_re_comp SmtRegLan.epsilon) = false := by
    rfl
  simp [hComp]

/-- On a nonempty valid word, removing epsilon does not change membership. -/
theorem in_nonemptyRe_iff
    (r : SmtRegLan) (s : native_String)
    (hValid : native_string_valid s = true) (hNe : s ≠ []) :
    RuleProofs.native_str_in_re s (nonemptyRe r) =
      RuleProofs.native_str_in_re s r := by
  rw [nonemptyRe, native_re_diff, RuleProofs.native_str_in_re_re_inter,
    RuleProofs.native_str_in_re_re_comp]
  have hEps : RuleProofs.native_str_in_re s SmtRegLan.epsilon = false := by
    cases s with
    | nil => exact False.elim (hNe rfl)
    | cons c cs =>
        rw [RuleProofs.native_str_in_re]
        simp only [hValid, ↓reduceIte, List.foldl_cons, native_re_deriv]
        exact RuleProofs.nativeListInRe_empty cs
  simp [hValid, hEps]

/-- The empty word is not in `nonemptyRe`. -/
theorem empty_not_in_nonemptyRe (r : SmtRegLan) :
    RuleProofs.native_str_in_re [] (nonemptyRe r) = false := by
  rw [nonemptyRe, native_re_diff, RuleProofs.native_str_in_re_re_inter,
    RuleProofs.native_str_in_re_re_comp]
  simp [RuleProofs.native_str_in_re, RuleProofs.nativeListInRe,
    native_string_valid, native_re_nullable]

private theorem valid_take (xs : native_String) (n : Nat)
    (h : native_string_valid xs = true) :
    native_string_valid (xs.take n) = true := by
  simp [native_string_valid] at h ⊢
  intro c hc
  exact h c (List.mem_of_mem_take hc)

private theorem valid_drop (xs : native_String) (n : Nat)
    (h : native_string_valid xs = true) :
    native_string_valid (xs.drop n) = true := by
  simp [native_string_valid] at h ⊢
  intro c hc
  exact h c (List.mem_of_mem_drop hc)

private theorem substr_of_ofNat_bounds
    (s : native_String) (j k : Nat)
    (hj : j < s.length) (hkPos : 0 < k)
    (hk : k ≤ s.length - j) :
    native_str_substr s (Int.ofNat j) (Int.ofNat k) =
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
  simpa [Int.ofNat_eq_natCast] using
    (show
      native_str_substr s (j : Int) (k : Int) =
        (s.drop j).take k by
      simp [native_str_substr, native_str_len, hStartNotNeg, hkZero, hjHigh,
        hMin])

private theorem substr_of_ofNat_bounds_nonneg
    (s : native_String) (j k : Nat)
    (hj : j ≤ s.length) (hk : k ≤ s.length - j) :
    native_str_substr s (Int.ofNat j) (Int.ofNat k) =
      (s.drop j).take k := by
  by_cases hk0 : k = 0
  · subst k
    simp [native_str_substr]
  · exact substr_of_ofNat_bounds s j k (by omega) (Nat.pos_of_ne_zero hk0) hk

private theorem in_re_cons
    (c : native_Char) (cs : native_String) (r : SmtRegLan)
    (hValid : native_string_valid (c :: cs) = true) :
    RuleProofs.native_str_in_re (c :: cs) r =
      RuleProofs.native_str_in_re cs (native_re_deriv c r) := by
  have hTail : native_string_valid cs = true := by
    simpa [native_string_valid, Bool.and_eq_true] using
      (show native_char_valid c = true ∧ native_string_valid cs = true by
        simpa [native_string_valid, Bool.and_eq_true] using hValid).2
  simp [RuleProofs.native_str_in_re, RuleProofs.nativeListInRe, hValid, hTail]

/-- A successful prefix search returns the shortest accepted prefix. -/
private theorem prefix_go_some_minimal (r : SmtRegLan) :
    ∀ (xs : native_String) (n found : Nat),
      native_string_valid xs = true →
      impl_native_re_prefix_match_len_go r xs n = some found →
      n ≤ found ∧ found ≤ n + xs.length ∧
        RuleProofs.native_str_in_re (xs.take (found - n)) r = true ∧
        ∀ k, k < found - n →
          RuleProofs.native_str_in_re (xs.take k) r = false
  | [], n, found, hValid, hFind => by
      simp only [impl_native_string_to_values, List.map_nil] at hFind
      rw [impl_native_re_prefix_match_len_go.eq_1] at hFind
      split at hFind
      · cases hFind
        simp [RuleProofs.native_str_in_re, RuleProofs.nativeListInRe,
          native_string_valid, *]
      · simp at hFind
  | c :: cs, n, found, hValid, hFind => by
      have hParts : native_char_valid c = true ∧
          native_string_valid cs = true := by
        simpa [native_string_valid] using hValid
      simp only [impl_native_string_to_values, List.map_cons] at hFind
      rw [impl_native_re_prefix_match_len_go.eq_2] at hFind
      split at hFind
      · cases hFind
        refine ⟨by simp, by simp, ?_, ?_⟩
        · simp [RuleProofs.native_str_in_re, RuleProofs.nativeListInRe,
            native_string_valid, *]
        · intro k hk
          omega
      · rename_i hNull
        have ih := prefix_go_some_minimal (native_re_deriv c r) cs (n + 1)
          found hParts.2 hFind
        rcases ih with ⟨hLo, hHi, hMatch, hMin⟩
        have hPos : n < found := by omega
        have hTake :
            (c :: cs).take (found - n) =
              c :: cs.take (found - (n + 1)) := by
          cases hDiff : found - n with
          | zero => omega
          | succ k =>
              have hk : k = found - (n + 1) := by omega
              simp [hDiff, hk]
        refine ⟨by omega, by simp only [List.length_cons]; omega, ?_, ?_⟩
        · rw [hTake, in_re_cons c (cs.take (found - (n + 1))) r]
          · exact hMatch
          · have hTakeValid := valid_take cs (found - (n + 1)) hParts.2
            simpa [native_string_valid, Bool.and_eq_true] using
              And.intro hParts.1 hTakeValid
        · intro k hk
          cases k with
          | zero =>
              have hsimpa := hNull
              try simp [RuleProofs.native_str_in_re, native_string_valid] at hsimpa ⊢
              exact hsimpa
          | succ k =>
              have hk' : k < found - (n + 1) := by omega
              rw [List.take_succ_cons,
                in_re_cons c (cs.take k) r]
              · exact hMin k hk'
              · have hTakeValid := valid_take cs k hParts.2
                simpa [native_string_valid, Bool.and_eq_true] using
                  And.intro hParts.1 hTakeValid

/-- Semantic specification of a successful positive prefix match. -/
theorem positive_prefix_some_spec
    (r : SmtRegLan) (xs : native_String) (len : Nat)
    (hValid : native_string_valid xs = true)
    (hFind : native_re_positive_prefix_match_len? r xs = some len) :
    0 < len ∧ len ≤ xs.length ∧
      RuleProofs.native_str_in_re (xs.take len) r = true ∧
      ∀ k, 0 < k → k < len →
        RuleProofs.native_str_in_re (xs.take k) r = false := by
  cases xs with
  | nil => simp [native_re_positive_prefix_match_len?] at hFind
  | cons c cs =>
      have hParts : native_char_valid c = true ∧
          native_string_valid cs = true := by
        simpa [native_string_valid] using hValid
      simp [native_re_positive_prefix_match_len?, hParts.1] at hFind
      cases hDer :
          native_re_prefix_match_len? (native_re_deriv c r) cs with
      | none => simp [hDer] at hFind
      | some n =>
          simp [hDer] at hFind
          subst len
          have hGo :
              impl_native_re_prefix_match_len_go (native_re_deriv c r) cs 0 =
                some n := by
            simpa [native_re_prefix_match_len?] using hDer
          have hSpec := prefix_go_some_minimal (native_re_deriv c r) cs 0 n
            hParts.2 hGo
          rcases hSpec with ⟨_, hBound, hMatch, hMin⟩
          refine ⟨by omega, by simp; omega, ?_, ?_⟩
          · rw [show (c :: cs).take (n + 1) = c :: cs.take n by simp]
            rw [in_re_cons c (cs.take n) r]
            · simpa using hMatch
            · have hTakeValid := valid_take cs n hParts.2
              simpa [native_string_valid, Bool.and_eq_true] using
                And.intro hParts.1 hTakeValid
          · intro k hkPos hkLt
            cases k with
            | zero => omega
            | succ k =>
                rw [List.take_succ_cons, in_re_cons c (cs.take k) r]
                · exact hMin k (by omega)
                · have hTakeValid := valid_take cs k hParts.2
                  simpa [native_string_valid, Bool.and_eq_true] using
                    And.intro hParts.1 hTakeValid

private theorem prefix_go_shift (r : SmtRegLan) :
    ∀ (xs : List SmtValue) (n : Nat),
      impl_native_re_prefix_match_len_go r xs n =
        (native_re_prefix_match_len? r xs).map (n + ·)
  | [], n => by
      rw [native_re_prefix_match_len?.eq_1,
        impl_native_re_prefix_match_len_go.eq_1,
        impl_native_re_prefix_match_len_go.eq_1]
      split <;> simp
  | c :: cs, n => by
      rw [native_re_prefix_match_len?.eq_1,
        impl_native_re_prefix_match_len_go.eq_2,
        impl_native_re_prefix_match_len_go.eq_2]
      split
      · simp
      · rw [prefix_go_shift (native_re_deriv c r) cs (n + 1),
          prefix_go_shift (native_re_deriv c r) cs 1]
        cases native_re_prefix_match_len? (native_re_deriv c r) cs <;>
          simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem prefix_match_eq_positive_of_not_nullable
    (r : SmtRegLan) (xs : List SmtValue)
    (hNull : native_re_nullable r = false) :
    native_re_prefix_match_len? r xs =
      native_re_positive_prefix_match_len? r xs := by
  cases xs with
  | nil =>
      simp [native_re_prefix_match_len?, impl_native_re_prefix_match_len_go,
        native_re_positive_prefix_match_len?, hNull]
  | cons c cs =>
      rw [native_re_prefix_match_len?.eq_1,
        impl_native_re_prefix_match_len_go.eq_2,
        native_re_positive_prefix_match_len?.eq_2]
      simp only [hNull, Bool.false_eq_true, if_false, Nat.zero_add]
      rw [prefix_go_shift (native_re_deriv c r) cs 1]
      cases native_re_prefix_match_len? (native_re_deriv c r) cs <;>
        simp [Nat.add_comm]

private theorem positive_prefix_congr_nonempty
    (r r' : SmtRegLan) :
    ∀ xs : native_String,
      native_string_valid xs = true →
      (∀ ys : native_String,
        ys ≠ [] →
        native_string_valid ys = true →
          RuleProofs.native_str_in_re ys r =
            RuleProofs.native_str_in_re ys r') →
      native_re_positive_prefix_match_len? r (impl_native_string_to_values xs) =
        native_re_positive_prefix_match_len? r' (impl_native_string_to_values xs)
  | [], _hValid, _hExt => rfl
  | c :: cs, hValid, hExt => by
      have hParts : native_char_valid c = true ∧
          native_string_valid cs = true := by
        simpa [native_string_valid] using hValid
      have hDerExt :
          ∀ ys : native_String,
            native_string_valid ys = true →
              CongSupport.native_str_in_re ys (native_re_deriv c r) =
                CongSupport.native_str_in_re ys (native_re_deriv c r') := by
        intro ys hys
        have hConsValid : native_string_valid (c :: ys) = true :=
          native_string_valid_cons hParts.1 hys
        change RuleProofs.native_str_in_re ys (native_re_deriv c r) =
          RuleProofs.native_str_in_re ys (native_re_deriv c r')
        rw [← in_re_cons c ys r hConsValid,
          ← in_re_cons c ys r' hConsValid]
        exact hExt (c :: ys) (by simp) hConsValid
      have hGo :=
        CongSupport.native_re_prefix_match_len_go_congr_valid_ext_of_str_ext
          cs (native_re_deriv c r) (native_re_deriv c r') 0 hParts.2 hDerExt
      have hPrefix := hGo
      change native_re_prefix_match_len?
          (native_re_deriv (SmtValue.Char c) r) (impl_native_string_to_values cs) =
        native_re_prefix_match_len?
          (native_re_deriv (SmtValue.Char c) r') (impl_native_string_to_values cs)
        at hPrefix
      simp only [impl_native_string_to_values] at hPrefix
      simp only [impl_native_string_to_values, List.map_cons,
        native_re_positive_prefix_match_len?]
      rw [hPrefix]

/-- Prefix matching against `r \ epsilon` is exactly positive prefix matching
against `r`. -/
theorem prefix_nonemptyRe_eq_positive
    (r : SmtRegLan) (xs : native_String)
    (hValid : native_string_valid xs = true) :
    native_re_prefix_match_len? (nonemptyRe r) (impl_native_string_to_values xs) =
      native_re_positive_prefix_match_len? r (impl_native_string_to_values xs) := by
  rw [prefix_match_eq_positive_of_not_nullable _ _
    (nonemptyRe_nullable_false r)]
  exact positive_prefix_congr_nonempty (nonemptyRe r) r xs hValid
    (fun ys hNe hys => in_nonemptyRe_iff r ys hys hNe)

private theorem positive_prefix_some_is_succ
    (r : SmtRegLan) (xs : List SmtValue) (n : Nat)
    (h : native_re_positive_prefix_match_len? r xs = some n) :
    ∃ k, n = k + 1 := by
  cases xs with
  | nil => simp [native_re_positive_prefix_match_len?] at h
  | cons c cs =>
      cases hm : native_re_prefix_match_len? (native_re_deriv c r) cs with
      | none => simp [native_re_positive_prefix_match_len?, hm] at h
      | some m =>
          simp [native_re_positive_prefix_match_len?, hm] at h
          subst n
          exact ⟨m, rfl⟩

/-- Searching with `r \ epsilon` is definitionally the same leftmost search as
the positive-match search used by replacement-all. -/
theorem find_nonempty_eq_find_nonemptyRe :
    ∀ (r : SmtRegLan) (xs : native_String) (idx : Nat),
      native_string_valid xs = true →
      impl_native_re_find_nonempty_idx_aux r (impl_native_string_to_values xs) idx =
        impl_native_re_find_idx_aux (nonemptyRe r) (impl_native_string_to_values xs) idx
  | r, [], idx, hValid => by
      have hPrefix := prefix_nonemptyRe_eq_positive r [] hValid
      simp only [impl_native_string_to_values, List.map_nil] at hPrefix ⊢
      rw [impl_native_re_find_nonempty_idx_aux.eq_def,
        impl_native_re_find_idx_aux.eq_def, hPrefix]
      simp [native_re_positive_prefix_match_len?]
  | r, c :: cs, idx, hValid => by
      have hParts : native_char_valid c = true ∧
          native_string_valid cs = true := by
        simpa [native_string_valid] using hValid
      have hPrefix := prefix_nonemptyRe_eq_positive r (c :: cs) hValid
      simp only [impl_native_string_to_values, List.map_cons] at hPrefix ⊢
      rw [impl_native_re_find_nonempty_idx_aux.eq_def,
        impl_native_re_find_idx_aux.eq_def, hPrefix]
      cases hPref : native_re_positive_prefix_match_len? r
          (SmtValue.Char c :: impl_native_string_to_values cs) with
      | none =>
          simp only [impl_native_string_to_values] at hPref
          simp only [hPref]
          simpa only [impl_native_string_to_values] using
            find_nonempty_eq_find_nonemptyRe r cs (idx + 1) hParts.2
      | some n =>
          simp only [impl_native_string_to_values] at hPref
          obtain ⟨k, rfl⟩ :=
            positive_prefix_some_is_succ r
              (SmtValue.Char c :: List.map SmtValue.Char cs) n hPref
          simp [hPref]

theorem find_nonempty_from_eq_find_nonemptyRe
    (r : SmtRegLan) (xs : native_String) (start : Nat)
    (hValid : native_string_valid xs = true) :
    impl_native_re_find_nonempty_idx_from r (impl_native_string_to_values xs) start =
      native_re_find_idx_from (nonemptyRe r) (impl_native_string_to_values xs) start := by
  unfold impl_native_re_find_nonempty_idx_from native_re_find_idx_from
  rw [← native_string_to_values_drop]
  exact find_nonempty_eq_find_nonemptyRe r (xs.drop start) start
    (valid_drop xs start hValid)

/-- A successful nonempty search returns a positive, in-bounds, shortest
match. -/
theorem find_nonempty_some_spec (r : SmtRegLan) :
    ∀ (xs : native_String) (base found len : Nat),
      native_string_valid xs = true →
      impl_native_re_find_nonempty_idx_aux r xs base = some (found, len) →
      base ≤ found ∧ found + len ≤ base + xs.length ∧ 0 < len ∧
        RuleProofs.native_str_in_re ((xs.drop (found - base)).take len) r = true ∧
        ∀ k, 0 < k → k < len →
          RuleProofs.native_str_in_re ((xs.drop (found - base)).take k) r = false
  | [], base, found, len, hValid, hFind => by
      simp [impl_native_string_to_values, impl_native_re_find_nonempty_idx_aux,
        native_re_positive_prefix_match_len?] at hFind
  | c :: cs, base, found, len, hValid, hFind => by
      have hParts : native_char_valid c = true ∧
          native_string_valid cs = true := by
        simpa [native_string_valid] using hValid
      simp only [impl_native_string_to_values, List.map_cons] at hFind
      rw [impl_native_re_find_nonempty_idx_aux.eq_def] at hFind
      cases hPref :
          native_re_positive_prefix_match_len? r
            (SmtValue.Char c :: impl_native_string_to_values cs) with
      | none =>
          simp only [impl_native_string_to_values] at hPref
          simp only [hPref] at hFind
          have ih := find_nonempty_some_spec r cs (base + 1) found len
            hParts.2 hFind
          rcases ih with ⟨hLo, hHi, hLen, hMatch, hMin⟩
          have hDrop :
              (c :: cs).drop (found - base) =
                cs.drop (found - (base + 1)) := by
            have : base + 1 ≤ found := hLo
            rw [show found - base = (found - (base + 1)) + 1 by omega]
            simp
          refine ⟨by omega, by simp only [List.length_cons]; omega,
            hLen, ?_, ?_⟩
          · simpa [hDrop] using hMatch
          · intro k hkPos hkLt
            simpa [hDrop] using hMin k hkPos hkLt
      | some matchLen =>
          simp only [impl_native_string_to_values] at hPref
          obtain ⟨k, rfl⟩ :=
            positive_prefix_some_is_succ r
              (SmtValue.Char c :: impl_native_string_to_values cs) matchLen hPref
          simp only [hPref, Option.some.injEq, Prod.mk.injEq] at hFind
          rcases hFind with ⟨rfl, rfl⟩
          have hSpec := positive_prefix_some_spec r (c :: cs) (k + 1)
            hValid hPref
          simpa using hSpec

private theorem find_nonempty_aux_add_offset
    (r : SmtRegLan) :
    ∀ (xs : List SmtValue) (off base : Nat),
      impl_native_re_find_nonempty_idx_aux r xs (base + off) =
        (impl_native_re_find_nonempty_idx_aux r xs off).map
          (fun p => (base + p.1, p.2))
  | [], off, base => by
      simp [impl_native_re_find_nonempty_idx_aux,
        native_re_positive_prefix_match_len?]
  | c :: cs, off, base => by
      rw [impl_native_re_find_nonempty_idx_aux.eq_def,
        impl_native_re_find_nonempty_idx_aux.eq_def]
      cases hPref :
          native_re_positive_prefix_match_len? r (c :: cs) with
      | none =>
          simp only [hPref]
          simpa [Nat.add_assoc] using
            find_nonempty_aux_add_offset r cs (off + 1) base
      | some n =>
          obtain ⟨k, rfl⟩ :=
            positive_prefix_some_is_succ r (c :: cs) n hPref
          simp

/-- Searching a suffix at offset zero is the shifted form of searching the
original string from that offset. -/
theorem find_nonempty_from_shift
    (r : SmtRegLan) (s : List SmtValue) (start : Nat) :
    impl_native_re_find_nonempty_idx_from r s start =
      (impl_native_re_find_nonempty_idx_from r (s.drop start) 0).map
        (fun p => (start + p.1, p.2)) := by
  unfold impl_native_re_find_nonempty_idx_from
  simpa using find_nonempty_aux_add_offset r (s.drop start) 0 start

/-- Once fuel exceeds the remaining string length, regex replacement-all is
independent of the precise fuel. -/
theorem replace_aux_fuel_irrel
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
                    cs fuel₁ fuel₂ (by simpa using h₁) (by simpa using h₂) rfl
              | some len =>
                  cases len with
                  | zero =>
                      apply congrArg (List.cons c)
                      exact ih cs.length (by omega)
                        cs fuel₁ fuel₂ (by simpa using h₁) (by simpa using h₂) rfl
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

theorem replace_aux_eq_replace_all_of_length_lt
    (r : SmtRegLan) (replacement xs : List SmtValue) (fuel : Nat)
    (hFuel : xs.length < fuel) :
    impl_native_re_replace_all_nonempty_list_aux fuel r replacement xs =
      impl_native_re_replace_all_nonempty_list r replacement xs := by
  unfold impl_native_re_replace_all_nonempty_list
  exact replace_aux_fuel_irrel r replacement xs fuel (xs.length + 1)
    hFuel (Nat.lt_succ_self xs.length)

theorem replace_all_eq_of_find_nonempty_idx_aux
    (r : SmtRegLan) (replacement xs : List SmtValue)
    (base found len : Nat)
    (hFind :
      impl_native_re_find_nonempty_idx_aux r xs base = some (found, len)) :
    ∃ gap : Nat,
      found = base + gap ∧
      impl_native_re_replace_all_nonempty_list r replacement xs =
        xs.take gap ++ replacement ++
          impl_native_re_replace_all_nonempty_list r replacement
            (xs.drop (gap + len)) := by
  generalize hn : xs.length = n
  induction n using Nat.strongRecOn generalizing xs base found len with
  | ind outerN ih =>
      cases xs with
      | nil =>
          simp [impl_native_re_find_nonempty_idx_aux,
            native_re_positive_prefix_match_len?] at hFind
      | cons c cs =>
          have hn' : cs.length + 1 = outerN := by
            simpa using hn
          rw [impl_native_re_find_nonempty_idx_aux] at hFind
          cases hPref :
              native_re_positive_prefix_match_len? r (c :: cs) with
          | none =>
              simp only [hPref] at hFind
              obtain ⟨gap, hFound, hReplace⟩ :=
                ih cs.length (by omega) cs (base + 1) found len hFind rfl
              refine ⟨1 + gap, ?_, ?_⟩
              · omega
              · change
                  impl_native_re_replace_all_nonempty_list_aux
                      ((c :: cs).length + 1) r replacement (c :: cs) = _
                rw [impl_native_re_replace_all_nonempty_list_aux.eq_3, hPref]
                change c :: impl_native_re_replace_all_nonempty_list r replacement cs = _
                have hTake :
                    (c :: cs).take (1 + gap) = c :: cs.take gap := by
                  simp [Nat.add_comm]
                have hDropIndex : 1 + gap + len = (gap + len) + 1 := by
                  omega
                rw [hTake, hDropIndex, List.drop_succ_cons]
                exact congrArg (List.cons c) hReplace
          | some matchLen =>
              cases matchLen with
              | zero =>
                  simp only [hPref] at hFind
                  obtain ⟨gap, hFound, hReplace⟩ :=
                    ih cs.length (by omega) cs (base + 1) found len hFind rfl
                  refine ⟨1 + gap, ?_, ?_⟩
                  · omega
                  · change
                      impl_native_re_replace_all_nonempty_list_aux
                          ((c :: cs).length + 1) r replacement (c :: cs) = _
                    rw [impl_native_re_replace_all_nonempty_list_aux.eq_3, hPref]
                    change c :: impl_native_re_replace_all_nonempty_list r replacement cs = _
                    have hTake :
                        (c :: cs).take (1 + gap) = c :: cs.take gap := by
                      simp [Nat.add_comm]
                    have hDropIndex : 1 + gap + len = (gap + len) + 1 := by
                      omega
                    rw [hTake, hDropIndex, List.drop_succ_cons]
                    exact congrArg (List.cons c) hReplace
              | succ k =>
                  rw [hPref] at hFind
                  simp only [Option.some.injEq, Prod.mk.injEq] at hFind
                  rcases hFind with ⟨hFound, hLen⟩
                  subst found
                  subst len
                  refine ⟨0, by simp, ?_⟩
                  unfold impl_native_re_replace_all_nonempty_list
                  rw [impl_native_re_replace_all_nonempty_list_aux.eq_3, hPref]
                  simp only [List.take_zero, List.nil_append, Nat.zero_add]
                  apply congrArg (List.append replacement)
                  exact replace_aux_fuel_irrel r replacement
                    ((c :: cs).drop (k + 1)) (c :: cs).length
                    (((c :: cs).drop (k + 1)).length + 1)
                    (by
                      simp only [List.length_drop, List.length_cons]
                      omega)
                    (Nat.lt_succ_self _)

/-- Replacement-all on a boundary suffix decomposes at the next scan match. -/
theorem replace_all_suffix_eq_of_find_nonempty_idx_from
    (s replacement : native_String) (r : SmtRegLan)
    (pos found len : Nat)
    (hFind :
      impl_native_re_find_nonempty_idx_from r s pos = some (found, len)) :
    native_str_replace_re_all (s.drop pos) r replacement =
      (s.drop pos).take (found - pos) ++ replacement ++
        native_str_replace_re_all (s.drop (found + len)) r replacement := by
  have hFindAux :
      impl_native_re_find_nonempty_idx_aux r (s.drop pos) pos =
        some (found, len) := by
    simpa [impl_native_re_find_nonempty_idx_from] using hFind
  obtain ⟨gap, hFound, hReplace⟩ :=
    replace_all_eq_of_find_nonempty_idx_aux r replacement (s.drop pos)
      pos found len hFindAux
  have hGap : found - pos = gap := by
    omega
  rw [hGap]
  change
    impl_native_re_replace_all_nonempty_list r replacement (s.drop pos) =
      (s.drop pos).take gap ++ replacement ++
        impl_native_re_replace_all_nonempty_list r replacement
          (s.drop (found + len))
  have hDrop :
      (s.drop pos).drop (gap + len) = s.drop (found + len) := by
    rw [List.drop_drop]
    congr 1
    omega
  have hDropValues := congrArg impl_native_string_to_values hDrop
  simp only [native_string_to_values_drop] at hDropValues
  rw [hReplace, hDropValues]
  simp only [native_string_to_values_take, native_string_to_values_drop]

theorem replace_all_eq_self_of_find_nonempty_idx_aux_none
    (r : SmtRegLan) (replacement xs : List SmtValue) (base : Nat)
    (hFind : impl_native_re_find_nonempty_idx_aux r xs base = none) :
    impl_native_re_replace_all_nonempty_list r replacement xs = xs := by
  induction xs generalizing base with
  | nil =>
      simp [impl_native_re_replace_all_nonempty_list,
        impl_native_re_replace_all_nonempty_list_aux,
        native_re_positive_prefix_match_len?]
  | cons c cs ih =>
      rw [impl_native_re_find_nonempty_idx_aux] at hFind
      cases hPref :
          native_re_positive_prefix_match_len? r (c :: cs) with
      | none =>
          simp only [hPref] at hFind
          have hTail := ih (base + 1) hFind
          change
            impl_native_re_replace_all_nonempty_list_aux
                ((c :: cs).length + 1) r replacement (c :: cs) =
              c :: cs
          rw [impl_native_re_replace_all_nonempty_list_aux.eq_3, hPref]
          change c :: impl_native_re_replace_all_nonempty_list r replacement cs =
            c :: cs
          rw [hTail]
      | some matchLen =>
          cases matchLen with
          | zero =>
              simp only [hPref] at hFind
              have hTail := ih (base + 1) hFind
              change
                impl_native_re_replace_all_nonempty_list_aux
                    ((c :: cs).length + 1) r replacement (c :: cs) =
                  c :: cs
              rw [impl_native_re_replace_all_nonempty_list_aux.eq_3, hPref]
              change c :: impl_native_re_replace_all_nonempty_list r replacement cs =
                c :: cs
              rw [hTail]
          | succ k =>
              simp [hPref] at hFind

theorem replace_all_suffix_eq_self_of_find_nonempty_idx_from_none
    (s replacement : native_String) (r : SmtRegLan) (pos : Nat)
    (hFind : impl_native_re_find_nonempty_idx_from r s pos = none) :
    native_str_replace_re_all (s.drop pos) r replacement = s.drop pos := by
  change impl_native_re_replace_all_nonempty_list r replacement (s.drop pos) =
    s.drop pos
  simpa only [native_string_to_values_drop] using
    (replace_all_eq_self_of_find_nonempty_idx_aux_none r
      (impl_native_string_to_values replacement)
      ((impl_native_string_to_values s).drop pos) pos (by
        simpa [impl_native_re_find_nonempty_idx_from] using hFind))

/-- Replacing each match by a one-character word rather than the empty word
changes the output length by exactly the number of scan matches. -/
theorem replace_all_length_diff_eq_scan_ends_aux
    (s one : native_String) (r : SmtRegLan)
    (hValid : native_string_valid s = true)
    (hOne : one.length = 1) :
    ∀ (fuel pos : Nat), pos ≤ s.length →
      s.length - pos < fuel →
      Int.ofNat (native_str_replace_re_all (s.drop pos) r one).length -
          Int.ofNat (native_str_replace_re_all (s.drop pos) r []).length =
        Int.ofNat (impl_native_re_scan_ends_aux fuel r s pos).length
  | 0, pos, hPos, hFuel => by omega
  | fuel + 1, pos, hPos, hFuel => by
      rw [impl_native_re_scan_ends_aux]
      cases hFind : impl_native_re_find_nonempty_idx_from r s pos with
      | none =>
          have hOneSelf :=
            replace_all_suffix_eq_self_of_find_nonempty_idx_from_none
              s one r pos hFind
          have hNilSelf :=
            replace_all_suffix_eq_self_of_find_nonempty_idx_from_none
              s [] r pos hFind
          simp only [native_string_to_values_nil] at hNilSelf
          rw [hOneSelf, hNilSelf]
          simp
      | some p =>
          rcases p with ⟨found, len⟩
          have hFindAux :
              impl_native_re_find_nonempty_idx_aux r (s.drop pos) pos =
                some (found, len) := by
            simpa [impl_native_re_find_nonempty_idx_from] using hFind
          have hDropValid : native_string_valid (s.drop pos) = true :=
            valid_drop s pos hValid
          have hSpec :=
            find_nonempty_some_spec r
              (s.drop pos) pos found len hDropValid (by
                simpa only [native_string_to_values_drop] using hFindAux)
          rcases hSpec with
            ⟨hFoundLo, hFoundHi, hLenPos, _hMatch, _hShortest⟩
          have hEndLo : pos < found + len := by omega
          have hEndHi : found + len ≤ s.length := by
            simp only [List.length_drop] at hFoundHi
            omega
          have hFuelTail : s.length - (found + len) < fuel := by
            omega
          have hOneRec :=
            replace_all_suffix_eq_of_find_nonempty_idx_from
              s one r pos found len hFind
          have hNilRec :=
            replace_all_suffix_eq_of_find_nonempty_idx_from
              s [] r pos found len hFind
          have hTail :=
            replace_all_length_diff_eq_scan_ends_aux s one r hValid hOne
              fuel (found + len) hEndHi hFuelTail
          have hGapLe : found - pos ≤ (s.drop pos).length := by
            omega
          have hTakeLen : ((s.drop pos).take (found - pos)).length =
              found - pos := by
            rw [List.length_take]
            exact Nat.min_eq_left hGapLe
          simp only [native_string_to_values_nil] at hNilRec
          rw [hOneRec, hNilRec]
          simp only [List.length_append, hOne, List.length_nil,
            List.length_cons, native_string_to_values_length, hTakeLen]
          simp only [Nat.add_zero, Int.ofNat_eq_natCast,
            Int.natCast_add, Int.natCast_one] at hTail ⊢
          omega

theorem replace_all_take_one_length_diff_eq_reEnds
    (s : native_String) (r : SmtRegLan)
    (hValid : native_string_valid s = true) :
    Int.ofNat (native_str_replace_re_all s r (s.take 1)).length -
        Int.ofNat (native_str_replace_re_all s r []).length =
      Int.ofNat (reEnds r s).length := by
  cases s with
  | nil =>
      simp [reEnds, native_str_replace_re_all,
        impl_native_re_replace_all_nonempty_list,
        impl_native_re_replace_all_nonempty_list_aux,
        impl_native_re_scan_ends_aux, impl_native_re_find_nonempty_idx_from,
        impl_native_re_find_nonempty_idx_aux,
        native_re_positive_prefix_match_len?]
  | cons c cs =>
      have hTakeOne : (List.take 1 (c :: cs)).length = 1 := by
        simp
      simpa [reEnds] using
        replace_all_length_diff_eq_scan_ends_aux (c :: cs)
          ((c :: cs).take 1) r hValid hTakeOne
          ((c :: cs).length + 1) 0 (Nat.zero_le _)
          (Nat.lt_succ_self _)

/-- Bounds and strict monotonicity of all endpoints returned by the native
scan. -/
private theorem scan_ends_aux_pairwise_bounds
    (r : SmtRegLan) (s : native_String)
    (hValid : native_string_valid s = true) :
    ∀ (fuel pos : Nat), pos ≤ s.length →
      let es := impl_native_re_scan_ends_aux fuel r s pos
      es.Pairwise (· < ·) ∧ ∀ e ∈ es, pos < e ∧ e ≤ s.length
  | 0, pos, hPos => by
      simp [impl_native_re_scan_ends_aux]
  | fuel + 1, pos, hPos => by
      rw [impl_native_re_scan_ends_aux]
      cases hFind : impl_native_re_find_nonempty_idx_from r s pos with
      | none => simp
      | some p =>
          rcases p with ⟨found, len⟩
          have hDropValid := valid_drop s pos hValid
          have hAux :
              impl_native_re_find_nonempty_idx_aux r (s.drop pos) pos =
                some (found, len) := by
            simpa [impl_native_re_find_nonempty_idx_from] using hFind
          have hSpec := find_nonempty_some_spec r (s.drop pos) pos found len
            hDropValid (by
              simpa only [native_string_to_values_drop] using hAux)
          rcases hSpec with ⟨hLo, hHi, hLen, _hMatch, _hMin⟩
          have hEndLo : pos < found + len := by omega
          have hEndHi : found + len ≤ s.length := by
            simpa [List.length_drop, hPos] using hHi
          have ih := scan_ends_aux_pairwise_bounds r s hValid fuel
            (found + len) hEndHi
          dsimp at ih
          refine ⟨?_, ?_⟩
          · simp only [List.pairwise_cons]
            exact ⟨fun e he => (ih.2 e he).1, ih.1⟩
          · intro e he
            simp only [List.mem_cons] at he
            rcases he with rfl | he
            · exact ⟨hEndLo, hEndHi⟩
            · exact ⟨Nat.lt_trans hEndLo (ih.2 e he).1, (ih.2 e he).2⟩

theorem reEnds_pairwise
    (r : SmtRegLan) (s : native_String)
    (hValid : native_string_valid s = true) :
    (reEnds r s).Pairwise (· < ·) := by
  exact (scan_ends_aux_pairwise_bounds r s hValid (s.length + 1) 0
    (Nat.zero_le _)).1

theorem reEnds_mem_bounds
    (r : SmtRegLan) (s : native_String)
    (hValid : native_string_valid s = true) :
    ∀ e ∈ reEnds r s, 0 < e ∧ e ≤ s.length := by
  exact (scan_ends_aux_pairwise_bounds r s hValid (s.length + 1) 0
    (Nat.zero_le _)).2

theorem reBound_mem
    (r : SmtRegLan) (s : native_String) (n : Nat)
    (h1 : 1 ≤ n) (h2 : n ≤ (reEnds r s).length) :
    reBound r s n ∈ reEnds r s := by
  cases n with
  | zero => omega
  | succ n =>
      rw [reBound_succ]
      exact StrReplaceAllSupport.getD_mem_of_lt _ n (by omega)

theorem reBound_le_length
    (r : SmtRegLan) (s : native_String)
    (hValid : native_string_valid s = true)
    (n : Nat) (hn : n ≤ (reEnds r s).length) :
    reBound r s n ≤ s.length := by
  cases n with
  | zero => simp [reBound_zero]
  | succ n =>
      exact (reEnds_mem_bounds r s hValid _
        (reBound_mem r s (n + 1) (by omega) hn)).2

theorem reBound_strict_mono
    (r : SmtRegLan) (s : native_String)
    (hValid : native_string_valid s = true)
    (n : Nat) (hn : n < (reEnds r s).length) :
    reBound r s n < reBound r s (n + 1) := by
  cases n with
  | zero =>
      rw [reBound_zero, reBound_succ]
      have hMem :=
        StrReplaceAllSupport.getD_mem_of_lt (reEnds r s) 0 hn
      exact (reEnds_mem_bounds r s hValid _ hMem).1
  | succ n =>
      rw [reBound_succ, reBound_succ]
      exact StrReplaceAllSupport.pairwise_getD_lt
        (reEnds r s) (reEnds_pairwise r s hValid) n (n + 1)
        (by omega) (by omega)

private theorem pairwise_interval_length
    (lo hi : Nat) :
    ∀ (l : List Nat),
      l.Pairwise (· < ·) →
      (∀ e ∈ l, lo < e ∧ e ≤ hi) →
      l.length ≤ hi - lo
  | [], hPair, hBounds => by simp
  | e :: es, hPair, hBounds => by
      have hPairParts := List.pairwise_cons.mp hPair
      have hHead := hBounds e (by simp)
      have hTailBounds : ∀ x ∈ es, e < x ∧ x ≤ hi := by
        intro x hx
        exact ⟨hPairParts.1 x hx, (hBounds x (by simp [hx])).2⟩
      have ih := pairwise_interval_length e hi es hPairParts.2 hTailBounds
      simp only [List.length_cons]
      omega

theorem reEnds_length_le
    (r : SmtRegLan) (s : native_String)
    (hValid : native_string_valid s = true) :
    (reEnds r s).length ≤ s.length := by
  exact pairwise_interval_length 0 s.length (reEnds r s)
    (reEnds_pairwise r s hValid) (reEnds_mem_bounds r s hValid)

private def scanSteps (r : SmtRegLan) (s : native_String) :
    Nat → List Nat → Prop
  | _prev, [] => True
  | prev, e :: es =>
      ∃ found len,
        impl_native_re_find_nonempty_idx_from r s prev = some (found, len) ∧
          e = found + len ∧ scanSteps r s e es

private theorem native_scan_has_steps
    (r : SmtRegLan) (s : native_String) :
    ∀ (fuel pos : Nat),
      scanSteps r s pos (impl_native_re_scan_ends_aux fuel r s pos)
  | 0, pos => by simp [impl_native_re_scan_ends_aux, scanSteps]
  | fuel + 1, pos => by
      rw [impl_native_re_scan_ends_aux]
      cases hFind : impl_native_re_find_nonempty_idx_from r s pos with
      | none => simp [scanSteps]
      | some p =>
          rcases p with ⟨found, len⟩
          exact ⟨found, len, hFind, rfl,
            native_scan_has_steps r s fuel (found + len)⟩

private theorem getD_default_irrel
    {α : Type} (l : List α) (n : Nat) (d d' : α)
    (hn : n < l.length) :
    l.getD n d = l.getD n d' := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hn, Option.getD_some, Option.getD_some]

/-- If a scan has enough fuel left to run past every endpoint it returned,
then its final boundary has no further nonempty match. -/
private theorem native_scan_last_find_none
    (r : SmtRegLan) (s : native_String) :
    ∀ (fuel pos : Nat),
      let es := impl_native_re_scan_ends_aux fuel r s pos
      es.length < fuel →
      impl_native_re_find_nonempty_idx_from r s
          ((pos :: es).getD es.length pos) = none
  | 0, pos => by
      simp [impl_native_re_scan_ends_aux]
  | fuel + 1, pos => by
      rw [impl_native_re_scan_ends_aux]
      cases hFind : impl_native_re_find_nonempty_idx_from r s pos with
      | none =>
          simp only [List.length_nil, List.getD_cons_zero]
          intro _
          exact hFind
      | some p =>
          rcases p with ⟨found, len⟩
          let tail := impl_native_re_scan_ends_aux fuel r s (found + len)
          have ih := native_scan_last_find_none r s fuel (found + len)
          dsimp only at ih
          change
            ((found + len) :: tail).length < fuel + 1 →
              impl_native_re_find_nonempty_idx_from r s
                  ((pos :: (found + len) :: tail).getD
                    ((found + len) :: tail).length pos) = none
          intro hLength
          have hTailLength : tail.length < fuel := by
            simp only [List.length_cons] at hLength
            omega
          have hLast := ih hTailLength
          have hInBounds :
              tail.length < ((found + len) :: tail).length := by simp
          simp only [List.length_cons, List.getD_cons_succ]
          rw [getD_default_irrel ((found + len) :: tail) tail.length pos
            (found + len) hInBounds]
          exact hLast

private theorem scanSteps_nth
    (r : SmtRegLan) (s : native_String) :
    ∀ (es : List Nat) (prev n : Nat),
      scanSteps r s prev es →
      n < es.length →
      ∃ found len,
        impl_native_re_find_nonempty_idx_from r s
            ((prev :: es).getD n prev) = some (found, len) ∧
          (prev :: es).getD (n + 1) prev = found + len
  | [], prev, n, hSteps, hn => by simp at hn
  | e :: es, prev, 0, hSteps, hn => by
      rcases hSteps with ⟨found, len, hFind, hE, hTail⟩
      exact ⟨found, len, by simpa using hFind, by simpa using hE⟩
  | e :: es, prev, n + 1, hSteps, hn => by
      rcases hSteps with ⟨found0, len0, hFind0, hE, hTail⟩
      have hnTail : n < es.length := by simpa using hn
      obtain ⟨found, len, hFind, hNext⟩ :=
        scanSteps_nth r s es e n hTail hnTail
      have hnCur : n < (e :: es).length := by
        simp only [List.length_cons]
        omega
      have hnNext : n + 1 < (e :: es).length := by simpa using hn
      refine ⟨found, len, ?_, ?_⟩
      · simpa only [List.getD_cons_succ,
          getD_default_irrel (e :: es) n prev e hnCur] using hFind
      · simpa only [List.getD_cons_succ, Nat.add_assoc,
          getD_default_irrel (e :: es) (n + 1) prev e hnNext] using hNext

/-- At every in-range occurrence number, the adjacent boundaries are exactly
the start-search position and end of the next shortest nonempty match. -/
theorem reBound_step
    (r : SmtRegLan) (s : native_String) (n : Nat)
    (hn : n < (reEnds r s).length) :
    ∃ found len,
      impl_native_re_find_nonempty_idx_from r s (reBound r s n) =
        some (found, len) ∧
      reBound r s (n + 1) = found + len := by
  exact scanSteps_nth r s (reEnds r s) 0 n
    (native_scan_has_steps r s (s.length + 1) 0) hn

theorem reBound_last_find_none
    (r : SmtRegLan) (s : native_String)
    (hValid : native_string_valid s = true) :
    impl_native_re_find_nonempty_idx_from r s
        (reBound r s (reEnds r s).length) = none := by
  have hLen : (reEnds r s).length < s.length + 1 := by
    have := reEnds_length_le r s hValid
    omega
  exact native_scan_last_find_none r s (s.length + 1) 0 hLen

/-- At the final boundary, filtered regex search reports no match and
replacement-all leaves the remaining suffix unchanged. -/
theorem reBound_last_spec
    (r : SmtRegLan) (s : native_String)
    (hValid : native_string_valid s = true) :
    native_str_indexof_re s (nonemptyRe r)
        (Int.ofNat (reBound r s (reEnds r s).length)) = -1 ∧
      ∀ replacement : native_String,
        native_str_replace_re_all
            (s.drop (reBound r s (reEnds r s).length)) r replacement =
          s.drop (reBound r s (reEnds r s).length) := by
  have hFind := reBound_last_find_none r s hValid
  have hBoundary :=
    reBound_le_length r s hValid (reEnds r s).length (Nat.le_refl _)
  constructor
  · have hStartNonneg :
        ¬ Int.ofNat (reBound r s (reEnds r s).length) < 0 :=
      Int.not_lt.mpr (Int.natCast_nonneg _)
    have hFindFiltered :
        native_re_find_idx_from (nonemptyRe r) s
            (reBound r s (reEnds r s).length) = none := by
      rw [← find_nonempty_from_eq_find_nonemptyRe r s _ hValid]
      exact hFind
    simp [native_str_indexof_re, hStartNonneg, hValid, hBoundary,
      hFindFiltered]
  · intro replacement
    exact replace_all_suffix_eq_self_of_find_nonempty_idx_from_none
      s replacement r (reBound r s (reEnds r s).length) hFind

/-- The native `str.indexof_re` on the epsilon-filtered regex returns the
start of the next scan match at an in-range boundary. -/
theorem indexof_nonemptyRe_at_reBound
    (r : SmtRegLan) (s : native_String)
    (hValid : native_string_valid s = true)
    (n : Nat) (hn : n < (reEnds r s).length) :
    ∃ len : Nat,
      0 < len ∧
      native_str_indexof_re s (nonemptyRe r)
          (Int.ofNat (reBound r s n)) =
        Int.ofNat (reBound r s (n + 1) - len) ∧
      reBound r s n ≤ reBound r s (n + 1) - len ∧
      RuleProofs.native_str_in_re
          (native_str_substr s
            (Int.ofNat (reBound r s (n + 1) - len))
            (Int.ofNat len)) r = true ∧
      (∀ k : Nat, 0 < k → k < len →
        RuleProofs.native_str_in_re
          (native_str_substr s
            (Int.ofNat (reBound r s (n + 1) - len))
            (Int.ofNat k)) r = false) := by
  obtain ⟨found, len, hFind, hEnd⟩ := reBound_step r s n hn
  have hBound := reBound_le_length r s hValid n (Nat.le_of_lt hn)
  have hDropValid := valid_drop s (reBound r s n) hValid
  have hAux :
      impl_native_re_find_nonempty_idx_aux r
          (s.drop (reBound r s n)) (reBound r s n) =
        some (found, len) := by
    simpa [impl_native_re_find_nonempty_idx_from] using hFind
  have hSpec := find_nonempty_some_spec r
    (s.drop (reBound r s n)) (reBound r s n) found len hDropValid (by
      simpa only [native_string_to_values_drop] using hAux)
  rcases hSpec with ⟨hFoundLo, hFoundHi, hLen, hMatch, hMin⟩
  have hFoundEnd : found = reBound r s (n + 1) - len := by omega
  rw [List.length_drop] at hFoundHi
  have hEndBound : found + len ≤ s.length := by omega
  have hFoundLe : found ≤ s.length := by omega
  have hIndex :
      native_str_indexof_re s (nonemptyRe r)
          (Int.ofNat (reBound r s n)) = Int.ofNat found := by
    have hStartNonneg : ¬ Int.ofNat (reBound r s n) < 0 :=
      Int.not_lt.mpr (Int.natCast_nonneg _)
    have hFindFiltered :
        native_re_find_idx_from (nonemptyRe r) s (reBound r s n) =
          some (found, len) := by
      rw [← find_nonempty_from_eq_find_nonemptyRe r s _ hValid]
      exact hFind
    simp [native_str_indexof_re, hStartNonneg, hValid, hBound,
      hFindFiltered]
  have hDropEq :
      (s.drop (reBound r s n)).drop
          (found - reBound r s n) = s.drop found := by
    rw [List.drop_drop]
    congr
    omega
  have hMatch' :
      RuleProofs.native_str_in_re ((s.drop found).take len) r = true := by
    simpa [hDropEq] using hMatch
  have hMin' :
      ∀ k, 0 < k → k < len →
        RuleProofs.native_str_in_re ((s.drop found).take k) r = false := by
    intro k hk hkLen
    simpa [hDropEq] using hMin k hk hkLen
  have hFoundLt : found < s.length := by omega
  have hLenBound : len ≤ s.length - found := by omega
  have hSubLen :
      native_str_substr s (Int.ofNat found) (Int.ofNat len) =
        (s.drop found).take len :=
    substr_of_ofNat_bounds s found len hFoundLt hLen hLenBound
  refine ⟨len, hLen, ?_, ?_, ?_, ?_⟩
  · simpa [hFoundEnd] using hIndex
  · omega
  · rw [← hFoundEnd]
    rw [hSubLen]
    exact hMatch'
  · intro k hk hkLen
    have hKBound : k ≤ s.length - found := by omega
    have hSubK :
        native_str_substr s (Int.ofNat found) (Int.ofNat k) =
          (s.drop found).take k :=
      substr_of_ofNat_bounds s found k hFoundLt hk hKBound
    rw [← hFoundEnd]
    rw [hSubK]
    exact hMin' k hk hkLen

/-- Full semantic package for one in-range scan step.  This is the native
counterpart of the quantified recurrence in the generated reduction
predicate. -/
theorem reBound_step_spec
    (r : SmtRegLan) (s : native_String)
    (hValid : native_string_valid s = true)
    (n : Nat) (hn : n < (reEnds r s).length) :
    ∃ start len : Nat,
      0 < len ∧
      reBound r s n ≤ start ∧
      start + len = reBound r s (n + 1) ∧
      native_str_indexof_re s (nonemptyRe r)
          (Int.ofNat (reBound r s n)) = Int.ofNat start ∧
      RuleProofs.native_str_in_re
          (native_str_substr s (Int.ofNat start) (Int.ofNat len))
          (nonemptyRe r) = true ∧
      (∀ k : Nat, 0 < k → k < len →
        RuleProofs.native_str_in_re
          (native_str_substr s (Int.ofNat start) (Int.ofNat k)) r =
            false) ∧
      ∀ replacement : native_String,
        native_str_replace_re_all (s.drop (reBound r s n)) r replacement =
          native_str_substr s (Int.ofNat (reBound r s n))
              (Int.ofNat (start - reBound r s n)) ++
            replacement ++
              native_str_replace_re_all
                (s.drop (reBound r s (n + 1))) r replacement := by
  obtain ⟨start, len, hFind, hEnd⟩ := reBound_step r s n hn
  have hBoundary := reBound_le_length r s hValid n (Nat.le_of_lt hn)
  have hDropValid := valid_drop s (reBound r s n) hValid
  have hAux :
      impl_native_re_find_nonempty_idx_aux r
          (s.drop (reBound r s n)) (reBound r s n) =
        some (start, len) := by
    simpa [impl_native_re_find_nonempty_idx_from] using hFind
  have hSpec := find_nonempty_some_spec r
    (s.drop (reBound r s n)) (reBound r s n) start len hDropValid (by
      simpa only [native_string_to_values_drop] using hAux)
  rcases hSpec with ⟨hStart, hEndBound0, hLen, hMatch0, hMin0⟩
  rw [List.length_drop] at hEndBound0
  have hEndBound : start + len ≤ s.length := by omega
  have hStartLt : start < s.length := by omega
  have hLenBound : len ≤ s.length - start := by omega
  have hDropStart :
      (s.drop (reBound r s n)).drop
          (start - reBound r s n) = s.drop start := by
    rw [List.drop_drop]
    congr
    omega
  have hMatch :
      RuleProofs.native_str_in_re ((s.drop start).take len) r = true := by
    simpa [hDropStart] using hMatch0
  have hMin :
      ∀ k, 0 < k → k < len →
        RuleProofs.native_str_in_re ((s.drop start).take k) r = false := by
    intro k hk hkLen
    simpa [hDropStart] using hMin0 k hk hkLen
  have hSubMatch :
      native_str_substr s (Int.ofNat start) (Int.ofNat len) =
        (s.drop start).take len :=
    substr_of_ofNat_bounds s start len hStartLt hLen hLenBound
  have hMatchValid :
      native_string_valid ((s.drop start).take len) = true :=
    valid_take (s.drop start) len (valid_drop s start hValid)
  have hMatchNe : (s.drop start).take len ≠ [] := by
    intro hNil
    have hTakeLen : ((s.drop start).take len).length = len := by
      simp [List.length_drop, Nat.min_eq_left hLenBound]
    rw [hNil] at hTakeLen
    simp at hTakeLen
    omega
  have hFilteredMatch :
      RuleProofs.native_str_in_re ((s.drop start).take len) (nonemptyRe r) = true := by
    rw [in_nonemptyRe_iff r _ hMatchValid hMatchNe]
    exact hMatch
  have hIndex :
      native_str_indexof_re s (nonemptyRe r)
          (Int.ofNat (reBound r s n)) = Int.ofNat start := by
    have hStartNonneg : ¬ Int.ofNat (reBound r s n) < 0 :=
      Int.not_lt.mpr (Int.natCast_nonneg _)
    have hFindFiltered :
        native_re_find_idx_from (nonemptyRe r) s (reBound r s n) =
          some (start, len) := by
      rw [← find_nonempty_from_eq_find_nonemptyRe r s _ hValid]
      exact hFind
    simp [native_str_indexof_re, hStartNonneg, hValid, hBoundary,
      hFindFiltered]
  have hGapBound :
      start - reBound r s n ≤ s.length - reBound r s n := by omega
  have hSubGap :
      native_str_substr s (Int.ofNat (reBound r s n))
          (Int.ofNat (start - reBound r s n)) =
        (s.drop (reBound r s n)).take
          (start - reBound r s n) :=
    substr_of_ofNat_bounds_nonneg s (reBound r s n)
      (start - reBound r s n) hBoundary hGapBound
  refine ⟨start, len, hLen, hStart, hEnd.symm, hIndex, ?_, ?_, ?_⟩
  · rw [hSubMatch]
    exact hFilteredMatch
  · intro k hk hkLen
    have hKBound : k ≤ s.length - start := by omega
    rw [substr_of_ofNat_bounds s start k hStartLt hk hKBound]
    exact hMin k hk hkLen
  · intro replacement
    have hReplace :=
      replace_all_suffix_eq_of_find_nonempty_idx_from s replacement r
        (reBound r s n) start len hFind
    rw [← hEnd] at hReplace
    rw [hSubGap]
    exact hReplace

theorem indexof_nonemptyRe_at_final_reBound_eq_neg_one
    (r : SmtRegLan) (s : native_String)
    (hValid : native_string_valid s = true) :
    native_str_indexof_re s (nonemptyRe r)
        (Int.ofNat (reBound r s (reEnds r s).length)) = -1 :=
  (reBound_last_spec r s hValid).1

theorem replace_all_at_final_reBound_eq_self
    (r : SmtRegLan) (s replacement : native_String)
    (hValid : native_string_valid s = true) :
    native_str_replace_re_all
        (s.drop (reBound r s (reEnds r s).length)) r replacement =
      s.drop (reBound r s (reEnds r s).length) :=
  (reBound_last_spec r s hValid).2 replacement

/-- Asking `str.substr` for the whole source length from an in-bounds
position returns the complete suffix at that position.  The requested
length is intentionally the source length (rather than the remaining
length), matching the generated `@strings_replace_re_all_result` term. -/
theorem full_substr_eq_drop
    (s : native_String) (boundary : Nat)
    (hBoundary : boundary ≤ s.length) :
    native_str_substr s (Int.ofNat boundary) (Int.ofNat s.length) =
      s.drop boundary := by
  by_cases hEmpty : s.length = 0
  · have hs : s = [] := List.eq_nil_of_length_eq_zero hEmpty
    subst s
    simp [native_str_substr, native_str_len]
  by_cases hFinal : boundary = s.length
  · subst boundary
    simp [native_str_substr, native_str_len]
  · have hBoundaryLt : boundary < s.length := by omega
    have hStartNonneg : ¬ (boundary : Int) < 0 :=
      Int.not_lt.mpr (Int.natCast_nonneg _)
    have hLengthPos : ¬ (s.length : Int) ≤ 0 := by omega
    have hStartLt : ¬ (s.length : Int) ≤ (boundary : Int) := by omega
    have hMin :
        min (s.length : Int)
            ((s.length : Int) - (boundary : Int)) =
          ((s.length - boundary : Nat) : Int) := by
      omega
    simp only [native_str_substr, native_str_len, Bool.or_eq_true,
      decide_eq_true_eq, Int.ofNat_eq_natCast]
    rw [if_neg]
    · rw [hMin, Int.toNat_natCast]
      exact List.take_of_length_le (by simp)
    · exact fun h =>
        h.elim (fun h => h.elim hStartNonneg hLengthPos)
          (fun h => hStartLt (of_decide_eq_true h))

/-- Native value of the generated replacement-result skolem at any
in-range scan boundary. -/
theorem replace_all_full_substr_at_reBound
    (r : SmtRegLan) (s replacement : native_String)
    (hValid : native_string_valid s = true)
    (n : Nat) (hn : n ≤ (reEnds r s).length) :
    native_str_replace_re_all
        (native_str_substr s (Int.ofNat (reBound r s n))
          (Int.ofNat s.length))
        r replacement =
      native_str_replace_re_all (s.drop (reBound r s n)) r replacement := by
  rw [full_substr_eq_drop s (reBound r s n)
    (reBound_le_length r s hValid n hn)]
  simp only [native_string_to_values_drop]

/-- The final generated replacement-result value is precisely the untouched
final suffix. -/
theorem replace_all_full_substr_at_final_reBound_eq_substr
    (r : SmtRegLan) (s replacement : native_String)
    (hValid : native_string_valid s = true) :
    native_str_replace_re_all
        (native_str_substr s
          (Int.ofNat (reBound r s (reEnds r s).length))
          (Int.ofNat s.length))
        r replacement =
      native_str_substr s
        (Int.ofNat (reBound r s (reEnds r s).length))
        (Int.ofNat s.length) := by
  rw [full_substr_eq_drop s _
      (reBound_le_length r s hValid _ (Nat.le_refl _))]
  simp only [native_string_to_values_drop]
  rw [replace_all_at_final_reBound_eq_self r s replacement hValid]
  rw [native_string_to_values_drop]

/-- Searching the final suffix locally from zero also reports no further
nonempty match.  This is the exact shape generated by the terminal EO
conjunct. -/
theorem indexof_nonemptyRe_on_final_suffix_eq_neg_one
    (r : SmtRegLan) (s : native_String)
    (hValid : native_string_valid s = true) :
    native_str_indexof_re
        (s.drop (reBound r s (reEnds r s).length))
        (nonemptyRe r) 0 = -1 := by
  let boundary := reBound r s (reEnds r s).length
  have hFind := reBound_last_find_none r s hValid
  have hShift := find_nonempty_from_shift r s boundary
  have hSuffixFind :
      impl_native_re_find_nonempty_idx_from r (s.drop boundary) 0 = none := by
    rw [hFind] at hShift
    cases h :
        impl_native_re_find_nonempty_idx_from r (s.drop boundary) 0 with
    | none => rfl
    | some p => simp [h] at hShift
  have hDropValid : native_string_valid (s.drop boundary) = true :=
    valid_drop s boundary hValid
  have hFiltered :
      native_re_find_idx_from (nonemptyRe r) (s.drop boundary) 0 = none := by
    have hEq := find_nonempty_from_eq_find_nonemptyRe r
      (s.drop boundary) 0 hDropValid
    simp only [native_string_to_values_drop] at hEq
    rw [← hEq]
    exact hSuffixFind
  change native_str_indexof_re (s.drop boundary) (nonemptyRe r) 0 = -1
  simp [native_str_indexof_re, hDropValid, hFiltered]

/-- The outer no-match branch of the generated predicate: if the initial
filtered search fails, replacement-all is the identity. -/
theorem replace_all_eq_self_of_initial_index_neg_one
    (r : SmtRegLan) (s replacement : native_String)
    (hValid : native_string_valid s = true)
    (hIndex :
      native_str_indexof_re s (nonemptyRe r) 0 = -1) :
    native_str_replace_re_all s r replacement = s := by
  have hFiltered :
      native_re_find_idx_from (nonemptyRe r) s 0 = none := by
    cases hFind : native_re_find_idx_from (nonemptyRe r) s 0 with
    | none => rfl
    | some p =>
        rcases p with ⟨found, len⟩
        simp [native_str_indexof_re, hValid, hFind] at hIndex
  have hFind :
      impl_native_re_find_nonempty_idx_from r s 0 = none := by
    rw [find_nonempty_from_eq_find_nonemptyRe r s 0 hValid]
    exact hFiltered
  simpa using
    (replace_all_suffix_eq_self_of_find_nonempty_idx_from_none
      s replacement r 0 hFind)

/-- If the outer no-match guard is false, the scan contains at least one
match, so the generated count is strictly positive. -/
theorem reEnds_length_pos_of_initial_index_ne_neg_one
    (r : SmtRegLan) (s : native_String)
    (hValid : native_string_valid s = true)
    (hIndex :
      native_str_indexof_re s (nonemptyRe r) 0 ≠ -1) :
    0 < (reEnds r s).length := by
  by_cases hPos : 0 < (reEnds r s).length
  · exact hPos
  · have hLen : (reEnds r s).length = 0 :=
      Nat.eq_zero_of_not_pos hPos
    have hFinal :=
      indexof_nonemptyRe_at_final_reBound_eq_neg_one r s hValid
    exact False.elim (hIndex (by simpa [hLen, reBound_zero] using hFinal))

/-- Named bundle of all native facts consumed by the EO proof of the
`str_replace_re_all` reduction branch. -/
structure NativeScanSpec (r : SmtRegLan) (s : native_String) : Prop where
  count :
    Int.ofNat (native_str_replace_re_all s r (s.take 1)).length -
        Int.ofNat (native_str_replace_re_all s r []).length =
      Int.ofNat (reEnds r s).length
  boundaryZero :
    native_str_occur_index_re s r 0 = 0
  finalIndex :
    native_str_indexof_re s (nonemptyRe r)
        (Int.ofNat (reBound r s (reEnds r s).length)) = -1
  finalReplace :
    ∀ replacement : native_String,
      native_str_replace_re_all
          (s.drop (reBound r s (reEnds r s).length)) r replacement =
        s.drop (reBound r s (reEnds r s).length)
  step :
    ∀ n : Nat, n < (reEnds r s).length →
      ∃ start len : Nat,
        0 < len ∧
        reBound r s n ≤ start ∧
        start + len = reBound r s (n + 1) ∧
        native_str_indexof_re s (nonemptyRe r)
            (Int.ofNat (reBound r s n)) = Int.ofNat start ∧
        RuleProofs.native_str_in_re
            (native_str_substr s (Int.ofNat start) (Int.ofNat len))
            (nonemptyRe r) = true ∧
        (∀ k : Nat, 0 < k → k < len →
          RuleProofs.native_str_in_re
            (native_str_substr s (Int.ofNat start) (Int.ofNat k)) r =
              false) ∧
        ∀ replacement : native_String,
          native_str_replace_re_all (s.drop (reBound r s n)) r replacement =
            native_str_substr s (Int.ofNat (reBound r s n))
                (Int.ofNat (start - reBound r s n)) ++
              replacement ++
                native_str_replace_re_all
                  (s.drop (reBound r s (n + 1))) r replacement

theorem native_scan_spec
    (r : SmtRegLan) (s : native_String)
    (hValid : native_string_valid s = true) :
    NativeScanSpec r s := by
  refine
    { count := replace_all_take_one_length_diff_eq_reEnds s r hValid
      boundaryZero := ?_
      finalIndex := indexof_nonemptyRe_at_final_reBound_eq_neg_one r s hValid
      finalReplace := replace_all_at_final_reBound_eq_self r s
        (hValid := hValid)
      step := fun n hn => reBound_step_spec r s hValid n hn }
  simpa [reBound_zero] using occur_index_re_ofNat_eq_reBound s r 0

end StrReplaceReAllReduction
