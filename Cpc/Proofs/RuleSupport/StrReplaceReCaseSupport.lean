module

public import Cpc.Proofs.RuleSupport.RegexIndexofSupport
import all Cpc.Proofs.RuleSupport.RegexIndexofSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport
public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport
public import Cpc.Proofs.RuleSupport.StrSubstrContainsSupport
import all Cpc.Proofs.RuleSupport.StrSubstrContainsSupport
public import Cpc.Proofs.Closed.IsClosedRec
import all Cpc.Proofs.Closed.IsClosedRec

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000
set_option maxRecDepth 12000

namespace StrReplaceReCase

/-! ### Native regex-search facts -/

private theorem native_re_str_valid_string (str : native_String) :
    native_re_str_valid (impl_native_string_to_values str) =
      native_string_valid str := by
  induction str with
  | nil => rfl
  | cons c cs ih =>
      change
        (native_char_valid c &&
          native_re_str_valid (impl_native_string_to_values cs)) =
        (native_char_valid c && native_string_valid cs)
      rw [ih]

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
  simp only [impl_native_string_to_values, List.map_cons] at hValueValid hTailValueValid ⊢
  simp [Smtm.native_str_in_re, hValueValid, hTailValueValid]

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

private theorem prefix_some_shortest (r : SmtRegLan) :
    ∀ (xs : native_String) (found : Nat),
      native_string_valid xs = true →
      native_re_prefix_match_len? r xs = some found →
      found ≤ xs.length ∧
        native_str_in_re (xs.take found) r = true ∧
        ∀ k, k < found →
          native_str_in_re (xs.take k) r = false
  | [], found, hValid, hFind => by
      simp only [impl_native_string_to_values, List.map] at hFind ⊢
      rw [native_re_prefix_match_len?.eq_1,
        impl_native_re_prefix_match_len_go.eq_1] at hFind
      split at hFind
      · rename_i hNull
        simp only [Option.some.injEq] at hFind
        subst found
        refine ⟨by simp, ?_, by omega⟩
        simpa [Smtm.native_str_in_re, native_re_str_valid] using hNull
      · simp at hFind
  | c :: cs, found, hValid, hFind => by
      have hParts : native_char_valid c = true ∧
          native_string_valid cs = true := by
        simpa [native_string_valid] using hValid
      simp only [impl_native_string_to_values, List.map] at hFind ⊢
      rw [native_re_prefix_match_len?.eq_1,
        impl_native_re_prefix_match_len_go.eq_2] at hFind
      split at hFind
      · rename_i hNull
        simp only [Option.some.injEq] at hFind
        subst found
        refine ⟨by simp, ?_, by omega⟩
        simpa [Smtm.native_str_in_re, native_re_str_valid] using hNull
      · rename_i hNull
        simp only [Nat.zero_add] at hFind
        have hShift := prefix_go_shift
          (native_re_deriv (SmtValue.Char c) r)
          (impl_native_string_to_values cs) 1
        simp only [impl_native_string_to_values] at hShift
        rw [hShift] at hFind
        cases hTail :
            native_re_prefix_match_len? (native_re_deriv (SmtValue.Char c) r)
              (impl_native_string_to_values cs) with
        | none =>
            simp only [impl_native_string_to_values] at hTail
            simp [hTail] at hFind
        | some n =>
            simp only [impl_native_string_to_values] at hTail
            simp [hTail] at hFind
            subst found
            have ih := prefix_some_shortest (native_re_deriv c r)
              cs n hParts.2 hTail
            rcases ih with ⟨hBound, hMatch, hShortest⟩
            refine ⟨by simp; omega, ?_, ?_⟩
            · have hTake :
                  (c :: cs).take (1 + n) = c :: cs.take n := by
                  simp [Nat.add_comm]
              have hTakeValues := congrArg (List.map SmtValue.Char) hTake
              simp only [List.map_take, List.map_cons] at hTakeValues
              rw [hTakeValues]
              have hCons := in_re_cons c (cs.take n) r
              simp only [impl_native_string_to_values, List.map_take] at hCons
              rw [hCons]
              · exact hMatch
              · have hTakeValid := valid_take cs n hParts.2
                simpa [native_string_valid, Bool.and_eq_true] using
                  And.intro hParts.1 hTakeValid
            · intro k hk
              cases k with
              | zero =>
                  simpa [Smtm.native_str_in_re, native_re_str_valid] using hNull
              | succ k =>
                  rw [List.take_succ_cons]
                  have hCons := in_re_cons c (cs.take k) r
                  simp only [impl_native_string_to_values, List.map_take] at hCons
                  rw [hCons]
                  · exact hShortest k (by omega)
                  · have hTakeValid := valid_take cs k hParts.2
                    simpa [native_string_valid, Bool.and_eq_true] using
                      And.intro hParts.1 hTakeValid

private theorem prefix_none_spec (r : SmtRegLan) :
    ∀ (xs : native_String),
      native_string_valid xs = true →
      native_re_prefix_match_len? r xs = none →
      ∀ k, k ≤ xs.length →
        native_str_in_re (xs.take k) r = false
  | [], hValid, hFind, k, hk => by
      have hk0 : k = 0 := by simpa using hk
      subst k
      simp only [impl_native_string_to_values, List.map] at hFind ⊢
      rw [native_re_prefix_match_len?.eq_1,
        impl_native_re_prefix_match_len_go.eq_1] at hFind
      split at hFind
      · simp at hFind
      · rename_i hNull
        simpa [Smtm.native_str_in_re, native_re_str_valid] using hNull
  | c :: cs, hValid, hFind, k, hk => by
      have hParts : native_char_valid c = true ∧
          native_string_valid cs = true := by
        simpa [native_string_valid] using hValid
      simp only [impl_native_string_to_values, List.map] at hFind ⊢
      rw [native_re_prefix_match_len?.eq_1,
        impl_native_re_prefix_match_len_go.eq_2] at hFind
      split at hFind
      · simp at hFind
      · rename_i hNull
        cases k with
        | zero =>
            simpa [Smtm.native_str_in_re, native_re_str_valid] using hNull
        | succ k =>
            rw [List.take_succ_cons]
            have hCons := in_re_cons c (cs.take k) r
            simp only [impl_native_string_to_values, List.map_take] at hCons
            rw [hCons]
            · apply prefix_none_spec (native_re_deriv c r) cs hParts.2
              · have hShift := prefix_go_shift
                    (native_re_deriv (SmtValue.Char c) r)
                    (impl_native_string_to_values cs) 1
                simp only [impl_native_string_to_values] at hShift
                simp only [Nat.zero_add] at hFind
                rw [hShift] at hFind
                cases hTail : native_re_prefix_match_len?
                    (native_re_deriv (SmtValue.Char c) r)
                    (impl_native_string_to_values cs) with
                | none => simp [impl_native_string_to_values]
                | some n =>
                    simp only [impl_native_string_to_values] at hTail
                    simp [hTail] at hFind
              · simpa using hk
            · have hTakeValid := valid_take cs k hParts.2
              simpa [native_string_valid, Bool.and_eq_true] using
                And.intro hParts.1 hTakeValid

private theorem find_some_shortest (r : SmtRegLan) :
    ∀ (xs : native_String) (idx found len : Nat),
      native_string_valid xs = true →
      impl_native_re_find_idx_aux r xs idx = some (found, len) →
      idx ≤ found ∧ found ≤ idx + xs.length ∧
        len ≤ (xs.drop (found - idx)).length ∧
        native_str_in_re ((xs.drop (found - idx)).take len) r = true ∧
        (∀ k, k < len →
          native_str_in_re ((xs.drop (found - idx)).take k) r = false)
  | [], idx, found, len, hValid, hFind => by
      simp only [impl_native_string_to_values, List.map] at hFind ⊢
      rw [impl_native_re_find_idx_aux.eq_def] at hFind
      cases hPref : native_re_prefix_match_len? r [] with
      | none => simp [hPref] at hFind
      | some n =>
          simp [hPref] at hFind
          obtain ⟨rfl, rfl⟩ := hFind
          have hSpec := prefix_some_shortest r [] n hValid hPref
          refine ⟨by simp, by simp, ?_, ?_, ?_⟩
          · simpa using hSpec.1
          · simpa [impl_native_string_to_values] using hSpec.2.1
          · simpa [impl_native_string_to_values] using hSpec.2.2
  | c :: cs, idx, found, len, hValid, hFind => by
      have hParts : native_char_valid c = true ∧
          native_string_valid cs = true := by
        simpa [native_string_valid] using hValid
      simp only [impl_native_string_to_values, List.map] at hFind ⊢
      rw [impl_native_re_find_idx_aux.eq_def] at hFind
      cases hPref : native_re_prefix_match_len? r (c :: cs) with
      | some n =>
          simp only [impl_native_string_to_values, List.map] at hPref
          simp [hPref] at hFind
          obtain ⟨rfl, rfl⟩ := hFind
          have hSpec := prefix_some_shortest r (c :: cs) n hValid hPref
          simp only [impl_native_string_to_values, List.map] at hSpec
          refine ⟨by simp, by simp, ?_, ?_, ?_⟩
          · simpa using hSpec.1
          · simpa using hSpec.2.1
          · simpa using hSpec.2.2
      | none =>
          simp only [impl_native_string_to_values, List.map] at hPref
          simp [hPref] at hFind
          have ih := find_some_shortest r cs (idx + 1) found len
            hParts.2 hFind
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
          · simpa [hDropFound, impl_native_string_to_values, List.map_drop,
              List.map_take] using hMatch
          · intro k hk
            simpa [hDropFound, impl_native_string_to_values, List.map_drop,
              List.map_take] using hMin k hk

private theorem prefix_ne_zero_of_nonnullable
    (r : SmtRegLan) (xs : List SmtValue) (n : Nat)
    (hNull : native_re_nullable r = false)
    (h : native_re_prefix_match_len? r xs = some n) :
    n ≠ 0 := by
  intro hn
  subst n
  rw [native_re_prefix_match_len?.eq_1] at h
  cases xs with
  | nil =>
      simp [impl_native_re_prefix_match_len_go.eq_1, hNull] at h
  | cons c cs =>
      simp [impl_native_re_prefix_match_len_go.eq_2, hNull] at h
      rw [prefix_go_shift (native_re_deriv c r) cs 1] at h
      cases native_re_prefix_match_len? (native_re_deriv c r) cs <;>
        simp at h

private theorem positive_prefix_eq_of_nonnullable
    (r : SmtRegLan) (xs : List SmtValue)
    (hNull : native_re_nullable r = false) :
    native_re_positive_prefix_match_len? r xs =
      native_re_prefix_match_len? r xs := by
  cases xs with
  | nil =>
      simp [native_re_positive_prefix_match_len?,
        native_re_prefix_match_len?, impl_native_re_prefix_match_len_go.eq_1,
        hNull]
  | cons c cs =>
      rw [native_re_positive_prefix_match_len?.eq_2]
      change _ = impl_native_re_prefix_match_len_go r (c :: cs) 0
      rw [impl_native_re_prefix_match_len_go.eq_2]
      simp only [hNull, ↓reduceIte, Nat.zero_add]
      rw [prefix_go_shift (native_re_deriv c r) cs 1]
      cases hPref :
          native_re_prefix_match_len? (native_re_deriv c r) cs <;>
        simp [hPref, Nat.add_comm]

private theorem find_nonempty_aux_eq_of_nonnullable
    (r : SmtRegLan) (hNull : native_re_nullable r = false) :
    ∀ (xs : List SmtValue) (idx : Nat),
      impl_native_re_find_nonempty_idx_aux r xs idx =
        impl_native_re_find_idx_aux r xs idx
  | [], idx => by
      rw [impl_native_re_find_nonempty_idx_aux.eq_def,
        impl_native_re_find_idx_aux.eq_def,
        positive_prefix_eq_of_nonnullable r [] hNull]
      simp [native_re_prefix_match_len?, impl_native_re_prefix_match_len_go.eq_1,
        hNull]
  | c :: cs, idx => by
      rw [impl_native_re_find_nonempty_idx_aux.eq_def,
        impl_native_re_find_idx_aux.eq_def,
        positive_prefix_eq_of_nonnullable r (c :: cs) hNull]
      cases hPref : native_re_prefix_match_len? r (c :: cs) with
      | none =>
          simp only [hPref]
          exact find_nonempty_aux_eq_of_nonnullable r hNull cs (idx + 1)
      | some n =>
          have hn := prefix_ne_zero_of_nonnullable r (c :: cs) n hNull hPref
          cases n with
          | zero => exact False.elim (hn rfl)
          | succ n => simp [hPref]

private theorem find_nonempty_from_eq_of_nonnullable
    (r : SmtRegLan) (s : native_String) (start : Nat)
    (hNull : native_re_nullable r = false) :
    impl_native_re_find_nonempty_idx_from r s start =
      native_re_find_idx_from r s start := by
  unfold impl_native_re_find_nonempty_idx_from native_re_find_idx_from
  exact find_nonempty_aux_eq_of_nonnullable r hNull
    ((impl_native_string_to_values s).drop start) start

private theorem prefix_zero_of_nullable
    (r : SmtRegLan) (xs : List SmtValue)
    (hNull : native_re_nullable r = true) :
    native_re_prefix_match_len? r xs = some 0 := by
  rw [native_re_prefix_match_len?.eq_1]
  cases xs with
  | nil => simp [impl_native_re_prefix_match_len_go.eq_1, hNull]
  | cons c cs => simp [impl_native_re_prefix_match_len_go.eq_2, hNull]

private theorem find_from_zero_of_nullable
    (r : SmtRegLan) (s : native_String)
    (hNull : native_re_nullable r = true) :
    native_re_find_idx_from r s 0 = some (0, 0) := by
  unfold native_re_find_idx_from
  rw [impl_native_re_find_idx_aux.eq_def,
    prefix_zero_of_nullable r
      (List.drop 0 (impl_native_string_to_values s)) hNull]

private theorem occur_index_re_zero
    (s : native_String) (r : SmtRegLan) :
    native_str_occur_index_re s r 0 = 0 := by
  simp [native_str_occur_index_re]

private theorem occur_index_re_one_of_find
    (s : native_String) (r : SmtRegLan) (idx len : Nat)
    (hFind : impl_native_re_find_nonempty_idx_from r s 0 = some (idx, len)) :
    native_str_occur_index_re s r 1 = Int.ofNat (idx + len) := by
  simp [native_str_occur_index_re, impl_native_re_scan_ends_aux, hFind]

private theorem occur_index_re_one_of_none
    (s : native_String) (r : SmtRegLan)
    (hFind : impl_native_re_find_nonempty_idx_from r s 0 = none) :
    native_str_occur_index_re s r 1 = -1 := by
  simp [native_str_occur_index_re, impl_native_re_scan_ends_aux, hFind]

private theorem substr_prefix_take
    (s : native_String) (idx : Nat) :
    native_str_substr s 0 (Int.ofNat idx) = s.take idx := by
  cases s with
  | nil => simp [native_str_substr, native_str_len]
  | cons c cs =>
      cases idx with
      | zero => simp [native_str_substr, native_str_len]
      | succ k =>
          by_cases hk : k ≤ cs.length
          · have hki : (k : Int) ≤ (cs.length : Int) :=
              Int.ofNat_le.mpr hk
            have hMin : min (k : Int) (cs.length : Int) = (k : Int) :=
              Int.min_eq_left hki
            simp [native_str_substr, native_str_len]
            rw [hMin]
            simp
          · have hkge : cs.length ≤ k := Nat.le_of_not_ge hk
            have hki : (cs.length : Int) ≤ (k : Int) :=
              Int.ofNat_le.mpr hkge
            have hMin :
                min (k : Int) (cs.length : Int) = (cs.length : Int) :=
              Int.min_eq_right hki
            have hTake : cs.take k = cs := List.take_of_length_le hkge
            simp [native_str_substr, native_str_len]
            rw [hMin]
            simp [hTake]

private theorem substr_middle
    (s : native_String) (idx len : Nat)
    (hIdx : idx < s.length) (hLen : len ≤ s.length - idx)
    (hPos : 0 < len) :
    native_str_substr s (Int.ofNat idx) (Int.ofNat len) =
      (s.drop idx).take len := by
  have hIdxNonneg : ¬ (Int.ofNat idx : Int) < 0 := by
    simp [Int.ofNat_eq_natCast]
  have hLenPos : ¬ (Int.ofNat len : Int) ≤ 0 := by
    simp only [Int.ofNat_eq_natCast]
    omega
  have hIdxHigh : ¬ (Int.ofNat idx : Int) ≥ Int.ofNat s.length := by
    simpa [Int.ofNat_eq_natCast] using hIdx
  have hMin :
      min (Int.ofNat len) (Int.ofNat s.length - Int.ofNat idx) =
        Int.ofNat len := by
    apply Int.min_eq_left
    have hIdxLe : idx ≤ s.length := Nat.le_of_lt hIdx
    simp only [Int.ofNat_eq_natCast]
    omega
  unfold native_str_substr native_str_len
  rw [if_neg]
  · rw [hMin]
    simp only [Int.ofNat_eq_natCast, Int.toNat_natCast]
  · simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact fun hBad => hBad.elim
      (fun h => h.elim hIdxNonneg hLenPos)
      hIdxHigh

private theorem substr_suffix_drop
    (s : native_String) (start : Nat) (hStart : start ≤ s.length) :
    native_str_substr s (Int.ofNat start)
        (Int.ofNat s.length - Int.ofNat start) =
      s.drop start := by
  by_cases hEq : start = s.length
  · subst start
    simp [native_str_substr, native_str_len]
  · have hLt : start < s.length := Nat.lt_of_le_of_ne hStart hEq
    have hStartNonneg : ¬ (Int.ofNat start : Int) < 0 := by
      simp [Int.ofNat_eq_natCast]
    have hLenPos :
        ¬ Int.ofNat s.length - Int.ofNat start ≤ 0 := by
      simp only [Int.ofNat_eq_natCast]
      omega
    have hStartHigh :
        ¬ (Int.ofNat start : Int) ≥ Int.ofNat s.length := by
      simpa [Int.ofNat_eq_natCast] using hLt
    unfold native_str_substr native_str_len
    rw [if_neg (by
      intro hBad
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hBad
      exact hBad.elim
        (fun h => h.elim hStartNonneg hLenPos)
        hStartHigh)]
    have hMin :
        min (Int.ofNat s.length - Int.ofNat start)
            (Int.ofNat s.length - Int.ofNat start) =
          Int.ofNat s.length - Int.ofNat start := by simp
    rw [hMin]
    have hDiff :
        Int.toNat (Int.ofNat s.length - Int.ofNat start) =
          s.length - start := by
      simp only [Int.ofNat_eq_natCast]
      omega
    simp only [Int.ofNat_eq_natCast, Int.toNat_natCast, hDiff]
    exact List.take_of_length_le (by simp)

private theorem take_append_middle_suffix
    (s : native_String) (idx len : Nat)
    (hBound : idx + len ≤ s.length) :
    s.take idx ++ (s.drop idx).take len ++ s.drop (idx + len) = s := by
  rw [← List.take_add]
  exact List.take_append_drop (idx + len) s

/-! ### SMT evaluation helpers -/

private theorem eval_boolean_term_eq (M : SmtModel) (b : native_Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_numeral_term_eq (M : SmtModel) (n : native_Int) :
    __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_var_term_eq
    (M : SmtModel) (s : native_String) (T : SmtType) :
    __smtx_model_eval M (SmtTerm.Var s T) =
      native_model_var_lookup M s T := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_purify_term_eq (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm._at_purify x) =
      __smtx_model_eval__at_purify (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_ite_term_eq
    (M : SmtModel) (a b c : SmtTerm) :
    __smtx_model_eval M (SmtTerm.ite a b c) =
      __smtx_model_eval_ite (__smtx_model_eval M a)
        (__smtx_model_eval M b) (__smtx_model_eval M c) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_eq_term_eq
    (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.eq a b) =
      __smtx_model_eval_eq (__smtx_model_eval M a)
        (__smtx_model_eval M b) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_lt_term_eq
    (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.lt a b) =
      __smtx_model_eval_lt (__smtx_model_eval M a)
        (__smtx_model_eval M b) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_str_in_re_term_eq
    (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_in_re a b) =
      __smtx_model_eval_str_in_re (__smtx_model_eval M a)
        (__smtx_model_eval M b) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_forall_encoding_true
    (M : SmtModel) (s : native_String) (T : SmtType) (body : SmtTerm)
    (hAll :
      ∀ v : SmtValue,
        __smtx_typeof_value v = T →
        __smtx_value_canonical v = true →
        __smtx_model_eval (native_model_push M s T v) body =
          SmtValue.Boolean true) :
    __smtx_model_eval M
        (SmtTerm.not (SmtTerm.exists s T (SmtTerm.not body))) =
      SmtValue.Boolean true := by
  classical
  have hNoSat :
      ¬ ∃ v : SmtValue,
        __smtx_typeof_value v = T ∧
        __smtx_value_canonical v = true ∧
        __smtx_model_eval (native_model_push M s T v)
            (SmtTerm.not body) = SmtValue.Boolean true := by
    rintro ⟨v, hvTy, hvCanonical, hvNot⟩
    have hvBody := hAll v hvTy hvCanonical
    simp [__smtx_model_eval, __smtx_model_eval_not, native_not,
      hvBody] at hvNot
  have hExistsEval :
      native_eval_exists M s T (SmtTerm.not body) =
        SmtValue.Boolean false := by
    change (if _h :
        ∃ v : SmtValue,
          __smtx_typeof_value v = T ∧
          __smtx_value_canonical v = true ∧
          __smtx_model_eval (native_model_push M s T v)
              (SmtTerm.not body) = SmtValue.Boolean true then
        SmtValue.Boolean true else SmtValue.Boolean false) =
      SmtValue.Boolean false
    rw [dif_neg hNoSat]
  change __smtx_model_eval_not
      (native_eval_exists M s T (SmtTerm.not body)) =
        SmtValue.Boolean true
  rw [hExistsEval]
  rfl

private theorem unpack_pack_string (s : native_String) :
    native_unpack_string (native_pack_string s) = s := by
  simp only [native_unpack_string, native_pack_string,
    Smtm.native_unpack_pack_seq, List.map_map]
  induction s with
  | nil => rfl
  | cons c cs ih => simp [impl_native_ssm_char_of_value, ih]

@[simp] private theorem unpack_seq_pack_string (s : native_String) :
    native_unpack_seq (native_pack_string s) =
      impl_native_string_to_values s := by
  simp [native_pack_string, impl_native_string_to_values,
    Smtm.native_unpack_pack_seq]

@[simp] private theorem elem_typeof_pack_string (s : native_String) :
    __smtx_elem_typeof_seq_value (native_pack_string s) =
      SmtType.Char := by
  unfold native_pack_string
  exact elem_typeof_pack_seq SmtType.Char _

@[simp] private theorem pack_values_eq_string (s : native_String) :
    native_pack_seq SmtType.Char (impl_native_string_to_values s) =
      native_pack_string s := by
  rfl

@[simp] private theorem pack_append_values_eq_string
    (s t : native_String) :
    native_pack_seq SmtType.Char
        (impl_native_string_to_values s ++ impl_native_string_to_values t) =
      native_pack_string (s ++ t) := by
  simp [native_pack_string, impl_native_string_to_values, List.map_append]

@[simp] private theorem pack_three_values_eq_string
    (s t u : native_String) :
    native_pack_seq SmtType.Char
        (impl_native_string_to_values s ++ impl_native_string_to_values t ++
          impl_native_string_to_values u) =
      native_pack_string (s ++ t ++ u) := by
  simp [native_pack_string, impl_native_string_to_values, List.map_append]

@[simp] private theorem pack_three_values_right_eq_string
    (s t u : native_String) :
    native_pack_seq SmtType.Char
        (impl_native_string_to_values s ++
          (impl_native_string_to_values t ++ impl_native_string_to_values u)) =
      native_pack_string (s ++ (t ++ u)) := by
  simp [native_pack_string, impl_native_string_to_values, List.map_append]

@[simp] private theorem native_string_to_values_length
    (s : native_String) :
    (impl_native_string_to_values s).length = s.length := by
  simp [impl_native_string_to_values]

private theorem unpack_pack_string_length (s : native_String) :
    (native_unpack_seq (native_pack_string s)).length = s.length := by
  simp [native_pack_string, Smtm.native_unpack_pack_seq]

private theorem pack_unpack_string
    (ss : SmtSeq)
    (hTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char) :
    native_pack_string (native_unpack_string ss) = ss := by
  have hTyped : list_typed SmtType.Char (native_unpack_seq ss) :=
    typed_unpack_seq_of_typeof_seq_value hTy
  have hMap :
      (native_unpack_seq ss).map
          (fun v => SmtValue.Char (impl_native_ssm_char_of_value v)) =
        native_unpack_seq ss := by
    generalize hl : native_unpack_seq ss = l at hTyped ⊢
    clear hl
    induction l with
    | nil => rfl
    | cons v vs ih =>
        rcases hTyped with ⟨hv, hvs⟩
        rcases char_value_canonical hv with ⟨c, rfl, _hc⟩
        simpa [impl_native_ssm_char_of_value] using ih hvs
  have hElem : __smtx_elem_typeof_seq_value ss = SmtType.Char :=
    elem_typeof_seq_value_of_typeof_seq_value hTy
  unfold native_pack_string native_unpack_string
  simp only [List.map_map]
  change native_pack_seq SmtType.Char
      ((native_unpack_seq ss).map
        (fun v => SmtValue.Char (impl_native_ssm_char_of_value v))) = ss
  rw [hMap]
  simpa [hElem] using native_pack_unpack_seq ss

private theorem extract_pack_string
    (s : native_String) (i n : native_Int) :
    native_pack_seq (__smtx_elem_typeof_seq_value (native_pack_string s))
        (native_seq_extract (native_unpack_seq (native_pack_string s)) i n) =
      native_pack_string (native_str_substr s i n) := by
  have hElem :
      __smtx_elem_typeof_seq_value (native_pack_string s) =
        SmtType.Char := by
    simp [native_pack_string, elem_typeof_pack_seq]
  rw [hElem]
  simp only [native_pack_string, native_seq_extract, native_str_substr,
    native_str_len, Smtm.native_unpack_pack_seq]
  simp only [List.length_map, apply_ite, List.map_nil,
    List.map_take, List.map_drop]
  split <;> simp_all
  -- v4.33 `simp_all` no longer pushes the `ite` through `List.map`, so the
  -- guard has to be discharged explicitly before the two sides line up.
  have hbadFalse :
      ¬ (((i < 0 ∨ n ≤ 0) ∨ ((s.length : Int)) ≤ i)) := by
    intro hbad
    rcases ‹(0 ≤ i ∧ 0 < n) ∧ i < Int.ofNat s.length› with
      ⟨⟨hi0, hn0⟩, hilt⟩
    rcases hbad with (hi | hn) | hlen
    · exact False.elim ((Int.not_lt_of_ge hi0) hi)
    · exact False.elim ((Int.not_le_of_gt hn0) hn)
    · exact False.elim ((Int.not_le_of_gt hilt) hlen)
  rw [if_neg hbadFalse]
  simp [List.map_take, List.map_drop]

private theorem unpack_extract_pack_string
    (s : native_String) (i n : native_Int) :
    native_unpack_string
        (native_pack_seq (__smtx_elem_typeof_seq_value (native_pack_string s))
          (native_seq_extract (native_unpack_seq (native_pack_string s)) i n)) =
      native_str_substr s i n := by
  have h := congrArg native_unpack_string (extract_pack_string s i n)
  simpa [unpack_pack_string] using h

private theorem eval_concat_packed
    (M : SmtModel) (a b : SmtTerm) (s t : native_String)
    (ha : __smtx_model_eval M a = SmtValue.Seq (native_pack_string s))
    (hb : __smtx_model_eval M b = SmtValue.Seq (native_pack_string t)) :
    __smtx_model_eval M (SmtTerm.str_concat a b) =
      SmtValue.Seq (native_pack_string (s ++ t)) := by
  rw [__smtx_model_eval.eq_def]
  simp [ha, hb, __smtx_model_eval_str_concat, native_seq_concat,
    native_pack_string, Smtm.native_unpack_pack_seq, elem_typeof_pack_seq,
    List.map_append]

private theorem eval_substr_packed
    (M : SmtModel) (a i n : SmtTerm) (s : native_String)
    (ii nn : native_Int)
    (ha : __smtx_model_eval M a = SmtValue.Seq (native_pack_string s))
    (hi : __smtx_model_eval M i = SmtValue.Numeral ii)
    (hn : __smtx_model_eval M n = SmtValue.Numeral nn) :
    __smtx_model_eval M (SmtTerm.str_substr a i n) =
      SmtValue.Seq (native_pack_string (native_str_substr s ii nn)) := by
  rw [__smtx_model_eval.eq_def]
  simp only [ha, hi, hn, __smtx_model_eval_str_substr]
  exact congrArg SmtValue.Seq (extract_pack_string s ii nn)

private theorem pack_string_injective :
    Function.Injective native_pack_string := by
  intro s t h
  have h' := congrArg native_unpack_string h
  simpa [unpack_pack_string] using h'

private theorem eo_is_closed_of_rec_nil
    (t : Term) (hNe : t ≠ Term.Stuck)
    (hRec :
      __eo_is_closed_rec t Term.__eo_List_nil = Term.Boolean true) :
    __eo_is_closed t = Term.Boolean true := by
  cases t <;> simp [__eo_is_closed] at hNe ⊢
  all_goals exact hRec

private theorem eo_is_closed_ternary_uop_args
    (op : UserOp) (x y z : Term)
    (hNotForall : op ≠ UserOp.forall)
    (hNotExists : op ≠ UserOp.exists)
    (hXNe : x ≠ Term.Stuck) (hYNe : y ≠ Term.Stuck)
    (hZNe : z ≠ Term.Stuck)
    (hClosed :
      __eo_is_closed
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z) =
        Term.Boolean true) :
    __eo_is_closed x = Term.Boolean true ∧
      __eo_is_closed y = Term.Boolean true ∧
        __eo_is_closed z = Term.Boolean true := by
  have hParentRec := eo_is_closed_eq_true_rec_nil hClosed
  have hArgsRec := eo_is_closed_rec_ternary_uop_eq_true_cases
    hNotForall hNotExists
    (hEnv := EoSmtVarEnvPerm.of_exact EoSmtVarEnv.nil) hParentRec
  exact ⟨eo_is_closed_of_rec_nil x hXNe hArgsRec.1,
    eo_is_closed_of_rec_nil y hYNe hArgsRec.2.1,
    eo_is_closed_of_rec_nil z hZNe hArgsRec.2.2⟩

/-! ### The `str_replace_re` reduction case -/

set_option maxHeartbeats 2000000 in
theorem str_replace_re_reduction_pred_true
    (M : SmtModel) (hM : model_wf M) (z y x : Term)
    (hTrans : RuleProofs.eo_has_smt_translation
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) z) y) x))
    (hClosed : __eo_is_closed
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) z) y)
          x) =
      Term.Boolean true) :
    eo_interprets M
      (__str_reduction_pred
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) z) y)
          x)) true := by
  let tz := __eo_to_smt z
  let ty := __eo_to_smt y
  let tx := __eo_to_smt x
  have hOrigNN :
      term_has_non_none_type (SmtTerm.str_replace_re tz ty tx) := by
    exact hTrans
  rcases str_replace_re_args_of_non_none (op := SmtTerm.str_replace_re)
      (typeof_str_replace_re_eq tz ty tx) hOrigNN with
    ⟨hzTy, hyTy, hxTy⟩
  have hZNN : term_has_non_none_type tz := by
    unfold term_has_non_none_type
    rw [hzTy]
    exact seq_ne_none SmtType.Char
  have hYNN : term_has_non_none_type ty := by
    unfold term_has_non_none_type
    rw [hyTy]
    decide
  have hXNN : term_has_non_none_type tx := by
    unfold term_has_non_none_type
    rw [hxTy]
    exact seq_ne_none SmtType.Char
  have hZTermNe : z ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation z (by
      exact hZNN)
  have hYTermNe : y ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y (by
      exact hYNN)
  have hXTermNe : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x (by
      exact hXNN)
  have hClosedArgs :
      __eo_is_closed z = Term.Boolean true ∧
        __eo_is_closed y = Term.Boolean true ∧
          __eo_is_closed x = Term.Boolean true := by
    apply eo_is_closed_ternary_uop_args UserOp.str_replace_re z y x
    · decide
    · decide
    · exact hZTermNe
    · exact hYTermNe
    · exact hXTermNe
    · exact hClosed
  let lenName := native_string_lit "@var.str_length"
  let lenVar := SmtTerm.Var lenName SmtType.Int
  let zero := SmtTerm.Numeral 0
  let one := SmtTerm.Numeral 1
  let empty := SmtTerm.String []
  let sourceLen := SmtTerm.str_len tz
  let finish := SmtTerm._at_strings_occur_index_re tz ty one
  let first := SmtTerm.str_indexof_re tz ty zero
  let preS := SmtTerm._at_purify (SmtTerm.str_substr tz zero first)
  let matched := SmtTerm._at_purify
    (SmtTerm.str_substr tz first (SmtTerm.neg finish first))
  let suffix := SmtTerm.str_concat
    (SmtTerm._at_purify
      (SmtTerm.str_substr tz finish (SmtTerm.neg sourceLen finish)))
    empty
  let result := SmtTerm._at_purify (SmtTerm.str_replace_re tz ty tx)
  let resultEq := SmtTerm.eq result
  let qMatch := SmtTerm.str_in_re
    (SmtTerm.str_substr matched zero lenVar) ty
  let qBody := SmtTerm.or (SmtTerm.not (SmtTerm.geq lenVar zero))
    (SmtTerm.or
      (SmtTerm.not (SmtTerm.lt lenVar (SmtTerm.str_len matched)))
      (SmtTerm.or (SmtTerm.not qMatch) (SmtTerm.Boolean false)))
  let shortest := SmtTerm.not
    (SmtTerm.exists lenName SmtType.Int (SmtTerm.not qBody))
  let nullable := SmtTerm.str_in_re empty ty
  let noMatch := SmtTerm.eq first (SmtTerm.Numeral (-1))
  let decomposition := SmtTerm.eq tz
    (SmtTerm.str_concat preS (SmtTerm.str_concat matched suffix))
  let replacementResult :=
    SmtTerm.str_concat preS (SmtTerm.str_concat tx suffix)
  let formula := SmtTerm.ite nullable
    (resultEq (SmtTerm.str_concat tx (SmtTerm.str_concat tz empty)))
    (SmtTerm.ite noMatch (resultEq tz)
      (SmtTerm.and decomposition
        (SmtTerm.and (SmtTerm.eq (SmtTerm.str_len preS) first)
          (SmtTerm.and shortest
            (SmtTerm.and (SmtTerm.str_in_re matched ty)
              (SmtTerm.and (resultEq replacementResult)
                (SmtTerm.Boolean true)))))))
  have hZeroTy : __smtx_typeof zero = SmtType.Int := by
    simp [zero, __smtx_typeof]
  have hOneTy : __smtx_typeof one = SmtType.Int := by
    simp [one, __smtx_typeof]
  have hEmptyTy : __smtx_typeof empty =
      SmtType.Seq SmtType.Char := by
    simp [empty, __smtx_typeof, native_string_valid, native_ite]
  have hSourceLenTy : __smtx_typeof sourceLen = SmtType.Int := by
    simp [sourceLen, typeof_str_len_eq, hzTy,
      __smtx_typeof_seq_op_1_ret]
  have hFinishTy : __smtx_typeof finish = SmtType.Int := by
    simp [finish, typeof_at_strings_occur_index_re_eq, hzTy, hyTy, hOneTy,
      native_ite, native_Teq]
  have hFirstTy : __smtx_typeof first = SmtType.Int := by
    simp [first, typeof_str_indexof_re_eq, hzTy, hyTy, hZeroTy,
      native_ite, native_Teq]
  have hPrefixTy : __smtx_typeof preS =
      SmtType.Seq SmtType.Char := by
    change __smtx_typeof (SmtTerm.str_substr tz zero first) =
      SmtType.Seq SmtType.Char
    simp [typeof_str_substr_eq, hzTy, hZeroTy, hFirstTy,
      __smtx_typeof_str_substr, native_ite, native_Teq]
  have hMatchedTy : __smtx_typeof matched =
      SmtType.Seq SmtType.Char := by
    change __smtx_typeof
        (SmtTerm.str_substr tz first (SmtTerm.neg finish first)) =
      SmtType.Seq SmtType.Char
    simp [typeof_str_substr_eq, typeof_neg_eq, hzTy, hFirstTy, hFinishTy,
      __smtx_typeof_str_substr, __smtx_typeof_arith_overload_op_2,
      native_ite, native_Teq]
  have hSuffixRawTy :
      __smtx_typeof
          (SmtTerm._at_purify
            (SmtTerm.str_substr tz finish
              (SmtTerm.neg sourceLen finish))) =
        SmtType.Seq SmtType.Char := by
    change __smtx_typeof
        (SmtTerm.str_substr tz finish (SmtTerm.neg sourceLen finish)) =
      SmtType.Seq SmtType.Char
    simp [typeof_str_substr_eq, typeof_neg_eq, hzTy, hFinishTy,
      hSourceLenTy, __smtx_typeof_str_substr,
      __smtx_typeof_arith_overload_op_2, native_ite, native_Teq]
  have hSuffixTy : __smtx_typeof suffix =
      SmtType.Seq SmtType.Char := by
    simp [suffix, typeof_str_concat_eq, hSuffixRawTy, hEmptyTy,
      __smtx_typeof_seq_op_2, native_ite, native_Teq]
  have hResultTy : __smtx_typeof result =
      SmtType.Seq SmtType.Char := by
    change __smtx_typeof (SmtTerm.str_replace_re tz ty tx) =
      SmtType.Seq SmtType.Char
    simp [typeof_str_replace_re_eq, hzTy, hyTy, hxTy,
      __smtx_typeof_seq_op_3, native_ite, native_Teq]
  have hLenVarTy : __smtx_typeof lenVar = SmtType.Int := by
    simp [lenVar, __smtx_typeof, __smtx_typeof_guard_wf,
      __smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
      native_and, native_ite]
  have hQMatchTy : __smtx_typeof qMatch = SmtType.Bool := by
    simp [qMatch, typeof_str_in_re_eq, typeof_str_substr_eq, hMatchedTy,
      hZeroTy, hLenVarTy, hyTy, __smtx_typeof_str_substr,
      __smtx_typeof_seq_op_2_ret, native_ite, native_Teq]
  have hQBodyTy : __smtx_typeof qBody = SmtType.Bool := by
    simp [qBody, typeof_or_eq, typeof_not_eq, typeof_geq_eq, typeof_lt_eq,
      typeof_str_len_eq, hLenVarTy, hZeroTy, hMatchedTy, hQMatchTy,
      __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_seq_op_1_ret,
      __smtx_typeof_guard, __smtx_typeof, native_ite, native_Teq]
  have hShortestTy : __smtx_typeof shortest = SmtType.Bool := by
    simp [shortest, typeof_not_eq, smtx_typeof_exists_term_eq, hQBodyTy,
      __smtx_typeof_guard, __smtx_typeof_guard_wf, __smtx_type_wf,
      __smtx_type_wf_component, __smtx_type_wf_rec, native_and,
      native_ite, native_Teq]
  have hNullableTy : __smtx_typeof nullable = SmtType.Bool := by
    simp [nullable, typeof_str_in_re_eq, hEmptyTy, hyTy,
      __smtx_typeof_seq_op_2_ret, native_ite, native_Teq]
  have hNoMatchTy : __smtx_typeof noMatch = SmtType.Bool := by
    simp [noMatch, typeof_eq_eq, hFirstTy, __smtx_typeof_eq,
      __smtx_typeof_guard, __smtx_typeof, native_ite, native_Teq]
  have hConcatSourceEmptyTy :
      __smtx_typeof (SmtTerm.str_concat tz empty) =
        SmtType.Seq SmtType.Char := by
    simp [typeof_str_concat_eq, hzTy, hEmptyTy, __smtx_typeof_seq_op_2,
      native_ite, native_Teq]
  have hNullableRhsTy :
      __smtx_typeof
          (SmtTerm.str_concat tx (SmtTerm.str_concat tz empty)) =
        SmtType.Seq SmtType.Char := by
    simp [typeof_str_concat_eq, hxTy, hConcatSourceEmptyTy,
      __smtx_typeof_seq_op_2, native_ite, native_Teq]
  have hMatchedSuffixTy :
      __smtx_typeof (SmtTerm.str_concat matched suffix) =
        SmtType.Seq SmtType.Char := by
    simp [typeof_str_concat_eq, hMatchedTy, hSuffixTy,
      __smtx_typeof_seq_op_2, native_ite, native_Teq]
  have hDecompositionRhsTy :
      __smtx_typeof
          (SmtTerm.str_concat preS (SmtTerm.str_concat matched suffix)) =
        SmtType.Seq SmtType.Char := by
    simp [typeof_str_concat_eq, hPrefixTy, hMatchedSuffixTy,
      __smtx_typeof_seq_op_2, native_ite, native_Teq]
  have hDecompositionTy :
      __smtx_typeof decomposition = SmtType.Bool := by
    simp [decomposition, typeof_eq_eq, hzTy, hDecompositionRhsTy,
      __smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq]
  have hTxSuffixTy :
      __smtx_typeof (SmtTerm.str_concat tx suffix) =
        SmtType.Seq SmtType.Char := by
    simp [typeof_str_concat_eq, hxTy, hSuffixTy, __smtx_typeof_seq_op_2,
      native_ite, native_Teq]
  have hReplacementResultTy :
      __smtx_typeof replacementResult = SmtType.Seq SmtType.Char := by
    simp [replacementResult, typeof_str_concat_eq, hPrefixTy, hTxSuffixTy,
      __smtx_typeof_seq_op_2, native_ite, native_Teq]
  have hPrefixLenEqTy :
      __smtx_typeof (SmtTerm.eq (SmtTerm.str_len preS) first) =
        SmtType.Bool := by
    simp [typeof_eq_eq, typeof_str_len_eq, hPrefixTy, hFirstTy,
      __smtx_typeof_seq_op_1_ret, __smtx_typeof_eq, __smtx_typeof_guard,
      native_ite, native_Teq]
  have hMatchedInReTy :
      __smtx_typeof (SmtTerm.str_in_re matched ty) = SmtType.Bool := by
    simp [typeof_str_in_re_eq, hMatchedTy, hyTy,
      __smtx_typeof_seq_op_2_ret, native_ite, native_Teq]
  have hResultEqZTy : __smtx_typeof (resultEq tz) = SmtType.Bool := by
    simp [resultEq, typeof_eq_eq, hResultTy, hzTy, __smtx_typeof_eq,
      __smtx_typeof_guard, native_ite, native_Teq]
  have hResultEqNullableTy :
      __smtx_typeof
          (resultEq (SmtTerm.str_concat tx (SmtTerm.str_concat tz empty))) =
        SmtType.Bool := by
    simp [resultEq, typeof_eq_eq, hResultTy, hNullableRhsTy,
      __smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq]
  have hResultEqReplacementTy :
      __smtx_typeof (resultEq replacementResult) = SmtType.Bool := by
    simp [resultEq, typeof_eq_eq, hResultTy, hReplacementResultTy,
      __smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq]
  have hResultTailTy :
      __smtx_typeof
          (SmtTerm.and (resultEq replacementResult)
            (SmtTerm.Boolean true)) =
        SmtType.Bool := by
    simp [typeof_and_eq, hResultEqReplacementTy, __smtx_typeof,
      native_ite]
  have hMatchTailTy :
      __smtx_typeof
          (SmtTerm.and (SmtTerm.str_in_re matched ty)
            (SmtTerm.and (resultEq replacementResult)
              (SmtTerm.Boolean true))) =
        SmtType.Bool := by
    simp [typeof_and_eq, hMatchedInReTy, hResultTailTy, native_ite]
  have hShortestTailTy :
      __smtx_typeof
          (SmtTerm.and shortest
            (SmtTerm.and (SmtTerm.str_in_re matched ty)
              (SmtTerm.and (resultEq replacementResult)
                (SmtTerm.Boolean true)))) =
        SmtType.Bool := by
    simp [typeof_and_eq, hShortestTy, hMatchTailTy, native_ite]
  have hPrefixTailTy :
      __smtx_typeof
          (SmtTerm.and (SmtTerm.eq (SmtTerm.str_len preS) first)
            (SmtTerm.and shortest
              (SmtTerm.and (SmtTerm.str_in_re matched ty)
                (SmtTerm.and (resultEq replacementResult)
                  (SmtTerm.Boolean true))))) =
        SmtType.Bool := by
    simp [typeof_and_eq, hPrefixLenEqTy, hShortestTailTy, native_ite]
  have hNonmatchBodyTy :
      __smtx_typeof
          (SmtTerm.and decomposition
            (SmtTerm.and (SmtTerm.eq (SmtTerm.str_len preS) first)
              (SmtTerm.and shortest
                (SmtTerm.and (SmtTerm.str_in_re matched ty)
                  (SmtTerm.and (resultEq replacementResult)
                    (SmtTerm.Boolean true)))))) =
        SmtType.Bool := by
    simp [typeof_and_eq, hDecompositionTy, hPrefixTailTy, native_ite]
  have hInnerIteTy :
      __smtx_typeof
          (SmtTerm.ite noMatch (resultEq tz)
            (SmtTerm.and decomposition
              (SmtTerm.and (SmtTerm.eq (SmtTerm.str_len preS) first)
                (SmtTerm.and shortest
                  (SmtTerm.and (SmtTerm.str_in_re matched ty)
                    (SmtTerm.and (resultEq replacementResult)
                      (SmtTerm.Boolean true))))))) =
        SmtType.Bool := by
    simp [typeof_ite_eq, hNoMatchTy, hResultEqZTy, hNonmatchBodyTy,
      __smtx_typeof_ite, native_ite, native_Teq]
  have hFormulaEq :
      __eo_to_smt
          (__str_reduction_pred
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_replace_re) z) y) x)) =
        formula := by
    simp only [__str_reduction_pred, __eo_mk_apply, hZTermNe, hYTermNe,
      hXTermNe]
    rfl
  change eo_interprets M
    (__str_reduction_pred
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) z) y) x))
      true
  apply RuleProofs.eo_interprets_of_bool_eval M _ true
  · unfold RuleProofs.eo_has_bool_type
    rw [hFormulaEq]
    simp [formula, typeof_ite_eq, hNullableTy, hResultEqNullableTy,
      hInnerIteTy, __smtx_typeof_ite, native_ite, native_Teq]
  · rw [hFormulaEq]
    clear hInnerIteTy hNonmatchBodyTy hPrefixTailTy hShortestTailTy
      hMatchTailTy hResultTailTy hResultEqReplacementTy
      hResultEqNullableTy hResultEqZTy hMatchedInReTy hPrefixLenEqTy
      hReplacementResultTy hTxSuffixTy hDecompositionTy
      hDecompositionRhsTy hMatchedSuffixTy hNullableRhsTy
      hConcatSourceEmptyTy hNoMatchTy hNullableTy hShortestTy hQBodyTy
      hQMatchTy hLenVarTy hResultTy hSuffixTy hSuffixRawTy hMatchedTy
      hPrefixTy hFirstTy hFinishTy hSourceLenTy hEmptyTy hOneTy hZeroTy
    have hZValTy :
        __smtx_typeof_value (__smtx_model_eval M tz) =
          SmtType.Seq SmtType.Char := by
      simpa [hzTy] using
        smt_model_eval_preserves_type_of_non_none M hM tz hZNN
    rcases seq_value_canonical hZValTy with ⟨sz, hZEval⟩
    have hSzTy :
        __smtx_typeof_seq_value sz = SmtType.Seq SmtType.Char := by
      simpa [hZEval, __smtx_typeof_value] using hZValTy
    let source := native_unpack_string sz
    have hSourceValid : native_string_valid source = true :=
      native_unpack_string_valid_of_typeof_seq_char hSzTy
    have hSourcePack : native_pack_string source = sz :=
      pack_unpack_string sz hSzTy
    have hZEvalString :
        __smtx_model_eval M tz =
          SmtValue.Seq (native_pack_string source) := by
      rw [hSourcePack]
      exact hZEval
    have hYValTy :
        __smtx_typeof_value (__smtx_model_eval M ty) =
          SmtType.RegLan := by
      simpa [hyTy] using
        smt_model_eval_preserves_type_of_non_none M hM ty hYNN
    rcases reglan_value_canonical hYValTy with ⟨regex, hYEval⟩
    have hXValTy :
        __smtx_typeof_value (__smtx_model_eval M tx) =
          SmtType.Seq SmtType.Char := by
      simpa [hxTy] using
        smt_model_eval_preserves_type_of_non_none M hM tx hXNN
    rcases seq_value_canonical hXValTy with ⟨sx, hXEval⟩
    have hSxTy :
        __smtx_typeof_seq_value sx = SmtType.Seq SmtType.Char := by
      simpa [hXEval, __smtx_typeof_value] using hXValTy
    let repl := native_unpack_string sx
    have hReplPack : native_pack_string repl = sx :=
      pack_unpack_string sx hSxTy
    have hXEvalString :
        __smtx_model_eval M tx =
          SmtValue.Seq (native_pack_string repl) := by
      rw [hReplPack]
      exact hXEval
    have hZeroEval :
        __smtx_model_eval M zero = SmtValue.Numeral 0 := by
      simp [zero, __smtx_model_eval]
    have hOneEval :
        __smtx_model_eval M one = SmtValue.Numeral 1 := by
      simp [one, __smtx_model_eval]
    have hEmptyEval :
        __smtx_model_eval M empty =
          SmtValue.Seq (native_pack_string []) := by
      simp [empty, __smtx_model_eval]
    have hNullableEval :
        __smtx_model_eval M nullable =
          SmtValue.Boolean (native_str_in_re [] regex) := by
      simp [nullable, __smtx_model_eval, __smtx_model_eval_str_in_re,
        hEmptyEval, hYEval, unpack_pack_string, impl_native_string_to_values]
    by_cases hEmptyMatch : native_str_in_re [] regex = true
    · have hRegexNullable : native_re_nullable regex = true := by
        simpa [Smtm.native_str_in_re, native_re_str_valid] using hEmptyMatch
      have hFind :
          native_re_find_idx_from regex source 0 = some (0, 0) :=
        find_from_zero_of_nullable regex source hRegexNullable
      have hNativeResult :
          native_str_replace_re source regex repl = repl ++ source := by
        simp [native_str_replace_re, hFind]
      have hResultEval :
          __smtx_model_eval M result =
            SmtValue.Seq (native_pack_string (repl ++ source)) := by
        simp [result, eval_purify_term_eq,
          __smtx_model_eval__at_purify, __smtx_model_eval_str_replace_re,
          hZEvalString, hYEval, hXEvalString, unpack_pack_string,
          hNativeResult, __smtx_model_eval]
      have hSourceEmptyEval :
          __smtx_model_eval M (SmtTerm.str_concat tz empty) =
            SmtValue.Seq (native_pack_string source) := by
        simpa using eval_concat_packed M tz empty source []
          hZEvalString hEmptyEval
      have hNullableRhsEval :
          __smtx_model_eval M
              (SmtTerm.str_concat tx (SmtTerm.str_concat tz empty)) =
            SmtValue.Seq (native_pack_string (repl ++ source)) :=
        eval_concat_packed M tx (SmtTerm.str_concat tz empty)
          repl source hXEvalString hSourceEmptyEval
      have hNullableEqEval :
          __smtx_model_eval M
              (resultEq
                (SmtTerm.str_concat tx (SmtTerm.str_concat tz empty))) =
            SmtValue.Boolean true := by
        rw [eval_eq_term_eq, hResultEval, hNullableRhsEval]
        exact RuleProofs.smtx_model_eval_eq_refl _
      rw [eval_ite_term_eq, hNullableEval, hEmptyMatch]
      exact hNullableEqEval
    · have hEmptyFalse : native_str_in_re [] regex = false := by
        cases h : native_str_in_re [] regex with
        | false => rfl
        | true => exact False.elim (hEmptyMatch h)
      have hRegexNonnullable : native_re_nullable regex = false := by
        simpa [Smtm.native_str_in_re, native_re_str_valid] using hEmptyFalse
      cases hFind : native_re_find_idx_from regex source 0 with
      | none =>
          have hFirstNative :
              native_str_indexof_re source regex 0 = -1 := by
            simp [native_str_indexof_re, hSourceValid, hFind]
          have hNativeResult :
              native_str_replace_re source regex repl = source := by
            simp [native_str_replace_re, hFind]
          have hFirstEval :
              __smtx_model_eval M first = SmtValue.Numeral (-1) := by
            simp [first, __smtx_model_eval,
              __smtx_model_eval_str_indexof_re, hZEvalString, hYEval,
              hZeroEval, unpack_pack_string, hFirstNative]
          have hResultEval :
              __smtx_model_eval M result =
                SmtValue.Seq (native_pack_string source) := by
            simp [result, eval_purify_term_eq,
              __smtx_model_eval__at_purify,
              __smtx_model_eval_str_replace_re, hZEvalString, hYEval,
              hXEvalString, unpack_pack_string, hNativeResult,
              __smtx_model_eval]
          have hNoMatchEval :
              __smtx_model_eval M noMatch = SmtValue.Boolean true := by
            rw [eval_eq_term_eq, hFirstEval]
            exact RuleProofs.smtx_model_eval_eq_refl _
          have hResultEqEval :
              __smtx_model_eval M (resultEq tz) =
                SmtValue.Boolean true := by
            rw [eval_eq_term_eq, hResultEval, hZEvalString]
            exact RuleProofs.smtx_model_eval_eq_refl _
          rw [eval_ite_term_eq, hNullableEval, hEmptyFalse]
          rw [eval_ite_term_eq, hNoMatchEval]
          exact hResultEqEval
      | some p =>
          rcases p with ⟨idx, matchLen⟩
          have hSpec := find_some_shortest regex source 0 idx matchLen
            hSourceValid (by simpa [native_re_find_idx_from] using hFind)
          rcases hSpec with
            ⟨_hIdxNonneg, hIdxBound, hLenBound, hMatch, hShortestNative⟩
          have hLenBound' : matchLen ≤ source.length - idx := by
            simpa [List.length_drop] using hLenBound
          have hMatch' :
              native_str_in_re ((source.drop idx).take matchLen) regex =
                true := by
            simpa [impl_native_string_to_values, List.map_take] using hMatch
          have hShortestNative' :
              ∀ k, k < matchLen →
                native_str_in_re ((source.drop idx).take k) regex = false := by
            intro k hk
            simpa [impl_native_string_to_values, List.map_take] using
              hShortestNative k hk
          have hMatchLenPos : 0 < matchLen := by
            apply Nat.pos_of_ne_zero
            intro hZero
            subst matchLen
            have : native_str_in_re [] regex = true := by
              simpa using hMatch'
            rw [hEmptyFalse] at this
            contradiction
          have hIdxLenBound : idx + matchLen ≤ source.length := by
            omega
          have hIdxLt : idx < source.length := by omega
          have hNonemptyFind :
              impl_native_re_find_nonempty_idx_from regex source 0 =
                some (idx, matchLen) := by
            rw [find_nonempty_from_eq_of_nonnullable regex source 0
              hRegexNonnullable]
            exact hFind
          have hFirstNative :
              native_str_indexof_re source regex 0 = Int.ofNat idx := by
            simp [native_str_indexof_re, hSourceValid, hFind]
          have hFinishNative :
              native_str_occur_index_re source regex 1 =
                Int.ofNat (idx + matchLen) :=
            occur_index_re_one_of_find source regex idx matchLen
              hNonemptyFind
          let preNative := source.take idx
          let matchNative := (source.drop idx).take matchLen
          let suffixNative := source.drop (idx + matchLen)
          have hPreNative :
              native_str_substr source 0 (Int.ofNat idx) = preNative := by
            simpa [preNative] using substr_prefix_take source idx
          have hEndDiff :
              Int.ofNat (idx + matchLen) - Int.ofNat idx =
                Int.ofNat matchLen := by
            simp only [Int.ofNat_eq_natCast]
            omega
          have hMatchNative :
              native_str_substr source (Int.ofNat idx)
                  (Int.ofNat (idx + matchLen) - Int.ofNat idx) =
                matchNative := by
            rw [hEndDiff]
            exact substr_middle source idx matchLen hIdxLt hLenBound'
              hMatchLenPos
          have hMatchNative' :
              native_str_substr source (Int.ofNat idx)
                  (Int.ofNat matchLen) =
                matchNative := by
            rw [← hEndDiff]
            exact hMatchNative
          have hSuffixNative :
              native_str_substr source (Int.ofNat (idx + matchLen))
                  (Int.ofNat source.length -
                    Int.ofNat (idx + matchLen)) =
                suffixNative := by
            exact substr_suffix_drop source (idx + matchLen) hIdxLenBound
          have hDecompNative :
              preNative ++ matchNative ++ suffixNative = source := by
            exact take_append_middle_suffix source idx matchLen hIdxLenBound
          have hFirstEval :
              __smtx_model_eval M first =
                SmtValue.Numeral (Int.ofNat idx) := by
            simp [first, __smtx_model_eval,
              __smtx_model_eval_str_indexof_re, hZEvalString, hYEval,
              hZeroEval, unpack_pack_string, hFirstNative]
          have hFinishEval :
              __smtx_model_eval M finish =
                SmtValue.Numeral (Int.ofNat (idx + matchLen)) := by
            simp [finish, __smtx_model_eval,
              __smtx_model_eval__at_strings_occur_index_re,
              hZEvalString, hYEval, hOneEval, unpack_pack_string,
              hFinishNative]
          have hSourceLenEval :
              __smtx_model_eval M sourceLen =
                SmtValue.Numeral (Int.ofNat source.length) := by
            simp [sourceLen, __smtx_model_eval,
              __smtx_model_eval_str_len, hZEvalString,
              native_seq_len, unpack_pack_string_length]
          have hDiffEval :
              __smtx_model_eval M (SmtTerm.neg finish first) =
                SmtValue.Numeral (Int.ofNat matchLen) := by
            simp [__smtx_model_eval, __smtx_model_eval__,
              hFinishEval, hFirstEval, native_zplus, native_zneg]
            exact hEndDiff
          have hSuffixLenEval :
              __smtx_model_eval M (SmtTerm.neg sourceLen finish) =
                SmtValue.Numeral
                  (Int.ofNat source.length -
                    Int.ofNat (idx + matchLen)) := by
            simp [__smtx_model_eval, __smtx_model_eval__,
              hSourceLenEval, hFinishEval, native_zplus, native_zneg,
              Int.sub_eq_add_neg]
          have hPreSubEval :
              __smtx_model_eval M (SmtTerm.str_substr tz zero first) =
                SmtValue.Seq (native_pack_string preNative) := by
            have h := eval_substr_packed M tz zero first source 0
              (Int.ofNat idx) hZEvalString hZeroEval hFirstEval
            rw [hPreNative] at h
            exact h
          have hPreEval :
              __smtx_model_eval M preS =
                SmtValue.Seq (native_pack_string preNative) := by
            simp [preS, eval_purify_term_eq,
              __smtx_model_eval__at_purify, hPreSubEval]
          have hMatchedSubEval :
              __smtx_model_eval M
                  (SmtTerm.str_substr tz first
                    (SmtTerm.neg finish first)) =
                SmtValue.Seq (native_pack_string matchNative) := by
            have h := eval_substr_packed M tz first
              (SmtTerm.neg finish first) source (Int.ofNat idx)
              (Int.ofNat matchLen) hZEvalString hFirstEval hDiffEval
            rw [hMatchNative'] at h
            exact h
          have hMatchedEval :
              __smtx_model_eval M matched =
                SmtValue.Seq (native_pack_string matchNative) := by
            simp [matched, eval_purify_term_eq,
              __smtx_model_eval__at_purify, hMatchedSubEval]
          have hSuffixSubEval :
              __smtx_model_eval M
                  (SmtTerm.str_substr tz finish
                    (SmtTerm.neg sourceLen finish)) =
                SmtValue.Seq (native_pack_string suffixNative) := by
            have h := eval_substr_packed M tz finish
              (SmtTerm.neg sourceLen finish) source
              (Int.ofNat (idx + matchLen))
              (Int.ofNat source.length - Int.ofNat (idx + matchLen))
              hZEvalString hFinishEval hSuffixLenEval
            rw [hSuffixNative] at h
            exact h
          have hSuffixPurifyEval :
              __smtx_model_eval M
                  (SmtTerm._at_purify
                    (SmtTerm.str_substr tz finish
                      (SmtTerm.neg sourceLen finish))) =
                SmtValue.Seq (native_pack_string suffixNative) := by
            simp [eval_purify_term_eq, __smtx_model_eval__at_purify,
              hSuffixSubEval]
          have hSuffixEval :
              __smtx_model_eval M suffix =
                SmtValue.Seq (native_pack_string suffixNative) := by
            simpa using eval_concat_packed M
              (SmtTerm._at_purify
                (SmtTerm.str_substr tz finish
                  (SmtTerm.neg sourceLen finish)))
              empty suffixNative [] hSuffixPurifyEval hEmptyEval
          have hFindValues := hFind
          simp only [impl_native_string_to_values] at hFindValues
          have hNativeResult :
              native_str_replace_re source regex repl =
                preNative ++ repl ++ suffixNative := by
            simp [native_str_replace_re, hFindValues, preNative, suffixNative,
              impl_native_string_to_values, List.map_take, List.map_drop]
          have hResultEval :
              __smtx_model_eval M result =
                SmtValue.Seq
                  (native_pack_string (preNative ++ repl ++ suffixNative)) := by
            simp [result, eval_purify_term_eq,
              __smtx_model_eval__at_purify,
              __smtx_model_eval_str_replace_re, hZEvalString, hYEval,
              hXEvalString, unpack_pack_string, hNativeResult,
              __smtx_model_eval]
          have hMatchSuffixEval :
              __smtx_model_eval M (SmtTerm.str_concat matched suffix) =
                SmtValue.Seq
                  (native_pack_string (matchNative ++ suffixNative)) :=
            eval_concat_packed M matched suffix matchNative suffixNative
              hMatchedEval hSuffixEval
          have hDecompRhsEval :
              __smtx_model_eval M
                  (SmtTerm.str_concat preS
                    (SmtTerm.str_concat matched suffix)) =
                SmtValue.Seq (native_pack_string source) := by
            have h := eval_concat_packed M preS
              (SmtTerm.str_concat matched suffix) preNative
              (matchNative ++ suffixNative) hPreEval hMatchSuffixEval
            rw [← List.append_assoc, hDecompNative] at h
            exact h
          have hTxSuffixEval :
              __smtx_model_eval M (SmtTerm.str_concat tx suffix) =
                SmtValue.Seq (native_pack_string (repl ++ suffixNative)) :=
            eval_concat_packed M tx suffix repl suffixNative
              hXEvalString hSuffixEval
          have hReplacementEval :
              __smtx_model_eval M replacementResult =
                SmtValue.Seq
                  (native_pack_string (preNative ++ repl ++ suffixNative)) := by
            simpa only [List.append_assoc] using
              (eval_concat_packed M preS (SmtTerm.str_concat tx suffix)
                preNative (repl ++ suffixNative) hPreEval hTxSuffixEval)
          have hNoMatchEval :
              __smtx_model_eval M noMatch = SmtValue.Boolean false := by
            simp [noMatch, eval_eq_term_eq, hFirstEval,
              __smtx_model_eval, __smtx_model_eval_eq, native_veq]
          have hDecompositionEval :
              __smtx_model_eval M decomposition =
                SmtValue.Boolean true := by
            rw [eval_eq_term_eq, hZEvalString, hDecompRhsEval]
            exact RuleProofs.smtx_model_eval_eq_refl _
          have hPreLenEval :
              __smtx_model_eval M (SmtTerm.str_len preS) =
                SmtValue.Numeral (Int.ofNat idx) := by
            simp [__smtx_model_eval, __smtx_model_eval_str_len, hPreEval,
              native_seq_len, preNative, unpack_pack_string_length,
              List.length_take,
              Nat.min_eq_left (Nat.le_of_lt hIdxLt)]
          have hPreLenEqEval :
              __smtx_model_eval M
                  (SmtTerm.eq (SmtTerm.str_len preS) first) =
                SmtValue.Boolean true := by
            rw [eval_eq_term_eq, hPreLenEval, hFirstEval]
            exact RuleProofs.smtx_model_eval_eq_refl _
          have hMatchedInReEval :
              __smtx_model_eval M (SmtTerm.str_in_re matched ty) =
                SmtValue.Boolean true := by
            have hMatchValues := hMatch'
            simp only [impl_native_string_to_values, List.map_drop] at hMatchValues
            simp [__smtx_model_eval, __smtx_model_eval_str_in_re,
              hMatchedEval, hYEval, unpack_pack_string, matchNative,
              impl_native_string_to_values, List.map_take, List.map_drop,
              hMatchValues]
          have hResultEqReplacementEval :
              __smtx_model_eval M (resultEq replacementResult) =
                SmtValue.Boolean true := by
            rw [eval_eq_term_eq, hResultEval, hReplacementEval]
            exact RuleProofs.smtx_model_eval_eq_refl _
          have hShortestEval :
              __smtx_model_eval M shortest = SmtValue.Boolean true := by
            apply eval_forall_encoding_true M lenName SmtType.Int qBody
            intro v hvTy _hvCanonical
            rcases int_value_canonical hvTy with ⟨k, rfl⟩
            let Mk := native_model_push M lenName SmtType.Int
              (SmtValue.Numeral k)
            change __smtx_model_eval Mk qBody = SmtValue.Boolean true
            have hAgree : model_agrees_on_globals M Mk :=
              model_agrees_on_globals_push M lenName SmtType.Int
                (SmtValue.Numeral k)
            have hZEvalPush :
                __smtx_model_eval Mk tz =
                  SmtValue.Seq (native_pack_string source) := by
              rw [← hZEvalString]
              exact
                (smt_model_eval_eq_of_eo_closed z hClosedArgs.1
                  M Mk hAgree).symm
            have hYEvalPush :
                __smtx_model_eval Mk ty = SmtValue.RegLan regex := by
              rw [← hYEval]
              exact
                (smt_model_eval_eq_of_eo_closed y hClosedArgs.2.1
                  M Mk hAgree).symm
            have hLenEval :
                __smtx_model_eval Mk lenVar = SmtValue.Numeral k := by
              simp [lenVar, Mk, eval_var_term_eq,
                native_model_var_lookup, native_model_push]
            have hZeroEvalPush :
                __smtx_model_eval Mk zero = SmtValue.Numeral 0 := by
              simp [zero, eval_numeral_term_eq]
            have hOneEvalPush :
                __smtx_model_eval Mk one = SmtValue.Numeral 1 := by
              simp [one, eval_numeral_term_eq]
            have hFirstEvalPush :
                __smtx_model_eval Mk first =
                  SmtValue.Numeral (Int.ofNat idx) := by
              simp [first, __smtx_model_eval,
                __smtx_model_eval_str_indexof_re, hZEvalPush, hYEvalPush,
                hZeroEvalPush, unpack_pack_string, hFirstNative]
            have hFinishEvalPush :
                __smtx_model_eval Mk finish =
                  SmtValue.Numeral (Int.ofNat (idx + matchLen)) := by
              simp [finish, __smtx_model_eval,
                __smtx_model_eval__at_strings_occur_index_re,
                hZEvalPush, hYEvalPush, hOneEvalPush, unpack_pack_string,
                hFinishNative]
            have hDiffEvalPush :
                __smtx_model_eval Mk (SmtTerm.neg finish first) =
                  SmtValue.Numeral (Int.ofNat matchLen) := by
              simp [__smtx_model_eval, __smtx_model_eval__,
                hFinishEvalPush, hFirstEvalPush, native_zplus, native_zneg]
              exact hEndDiff
            have hMatchedSubEvalPush :
                __smtx_model_eval Mk
                    (SmtTerm.str_substr tz first
                      (SmtTerm.neg finish first)) =
                  SmtValue.Seq (native_pack_string matchNative) := by
              have h := eval_substr_packed Mk tz first
                (SmtTerm.neg finish first) source (Int.ofNat idx)
                (Int.ofNat matchLen) hZEvalPush hFirstEvalPush
                hDiffEvalPush
              rw [hMatchNative'] at h
              exact h
            have hMatchedEvalPush :
                __smtx_model_eval Mk matched =
                  SmtValue.Seq (native_pack_string matchNative) := by
              simp [matched, eval_purify_term_eq,
                __smtx_model_eval__at_purify, hMatchedSubEvalPush]
            have hMatchNativeLength : matchNative.length = matchLen := by
              simp [matchNative, List.length_take,
                Nat.min_eq_left hLenBound']
            have hMatchedLenEvalPush :
                __smtx_model_eval Mk (SmtTerm.str_len matched) =
                  SmtValue.Numeral (Int.ofNat matchLen) := by
              simp [__smtx_model_eval, __smtx_model_eval_str_len,
                hMatchedEvalPush, native_seq_len, unpack_pack_string_length,
                hMatchNativeLength]
            have hQSubEval :
                __smtx_model_eval Mk
                    (SmtTerm.str_substr matched zero lenVar) =
                  SmtValue.Seq
                    (native_pack_string
                      (native_str_substr matchNative 0 k)) :=
              eval_substr_packed Mk matched zero lenVar matchNative 0 k
                hMatchedEvalPush hZeroEvalPush hLenEval
            have hQMatchEval :
                __smtx_model_eval Mk qMatch =
                  SmtValue.Boolean
                    (native_str_in_re
                      (native_str_substr matchNative 0 k) regex) := by
              simp only [qMatch]
              rw [eval_str_in_re_term_eq, hQSubEval, hYEvalPush]
              simp [__smtx_model_eval_str_in_re, unpack_pack_string,
                impl_native_string_to_values]
            have hQBodyEval :
                __smtx_model_eval Mk qBody =
                  SmtValue.Boolean
                    (native_or (native_not (native_zleq 0 k))
                      (native_or
                        (native_not
                          (native_zlt k (Int.ofNat matchLen)))
                        (native_or
                          (native_not
                            (native_str_in_re
                              (native_str_substr matchNative 0 k) regex))
                          false))) := by
              simp only [qBody, smtx_eval_or_term_eq,
                smtx_eval_not_term_eq,
                StrSubstrContainsSupport.smtx_eval_geq_term_eq,
                eval_lt_term_eq, smtx_eval_str_len_term_eq,
                hLenEval, hZeroEvalPush, hMatchedLenEvalPush,
                hQMatchEval, eval_boolean_term_eq]
              rfl
            rw [hQBodyEval]
            by_cases hkNonneg : 0 ≤ k
            · by_cases hkLt : k < Int.ofNat matchLen
              · have hkNatCast : (k.toNat : Int) = k :=
                  Int.toNat_of_nonneg hkNonneg
                have hkNat : k.toNat < matchLen := by
                  exact_mod_cast (show
                    (k.toNat : Int) < (matchLen : Int) by
                      simpa [hkNatCast] using hkLt)
                have hSub :
                    native_str_substr matchNative 0 k =
                      (source.drop idx).take k.toNat := by
                  calc
                    native_str_substr matchNative 0 k =
                        matchNative.take k.toNat := by
                      rw [← hkNatCast]
                      exact substr_prefix_take matchNative k.toNat
                    _ = (source.drop idx).take k.toNat := by
                      simp [matchNative, List.take_take,
                        Nat.min_eq_left (Nat.le_of_lt hkNat)]
                have hQFalse :
                    native_str_in_re
                        (native_str_substr matchNative 0 k) regex =
                      false := by
                  rw [hSub]
                  simpa [impl_native_string_to_values, List.map_take] using
                    hShortestNative' k.toNat hkNat
                simp [native_or, native_not, native_zleq, native_zlt,
                  hkNonneg, hkLt, hQFalse]
              · have hkGe : Int.ofNat matchLen ≤ k :=
                  Int.le_of_not_gt hkLt
                simp [native_or, native_not, native_zleq, native_zlt,
                  hkNonneg, hkGe]
                exact Or.inl (by
                  simpa [Int.ofNat_eq_natCast] using hkGe)
            · simp [native_or, native_not, native_zleq, native_zlt,
                hkNonneg]
          rw [eval_ite_term_eq, hNullableEval, hEmptyFalse]
          simp only [__smtx_model_eval_ite]
          rw [eval_ite_term_eq, hNoMatchEval]
          simp only [__smtx_model_eval_ite]
          rw [smtx_eval_and_term_eq, hDecompositionEval]
          rw [smtx_eval_and_term_eq, hPreLenEqEval]
          rw [smtx_eval_and_term_eq, hShortestEval]
          rw [smtx_eval_and_term_eq, hMatchedInReEval]
          rw [smtx_eval_and_term_eq, hResultEqReplacementEval,
            eval_boolean_term_eq]
          rfl

end StrReplaceReCase
