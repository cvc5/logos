module

public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

/-!
Shared native-sequence `indexof`/`extract`/`contains` reasoning toolkit.

These lemmas relate `native_seq_indexof` / `native_seq_contains` /
`native_seq_extract` to concrete list decompositions.  They were previously
proved privately (and redundantly) inside individual support and rule files
(e.g. `ConcatSplitSupport`, `String_eager_reduction`); they are collected here
as a low-level leaf so that downstream files can depend on a single common
support file rather than importing one another.
-/

theorem int_nonneg_of_not_neg {i : native_Int} (hi : ¬ i < 0) :
    0 ≤ i := by
  cases i with
  | ofNat n =>
      simp
  | negSucc n =>
      exfalso
      exact hi (by simp)

/-! The executable sequence search now delegates to the regular-expression
matcher.  The following lemmas connect an exact-list regular expression back
to the structurally recursive list scanner used throughout these proofs. -/

theorem native_re_concat_char_eq
    (c : SmtValue) (r : SmtRegLan)
    (hEmpty : r ≠ SmtRegLan.empty) (hEpsilon : r ≠ SmtRegLan.epsilon) :
    native_re_concat (SmtRegLan.char c) r =
      SmtRegLan.concat (SmtRegLan.char c) r := by
  cases r <;> simp_all [native_re_concat]

theorem native_re_of_list_cons_ne :
    ∀ (c : SmtValue) (cs : List SmtValue),
      impl_native_re_of_list (c :: cs) ≠ SmtRegLan.empty ∧
        impl_native_re_of_list (c :: cs) ≠ SmtRegLan.epsilon
  | c, [] => by
      simp [impl_native_re_of_list, native_re_concat]
  | c, d :: ds => by
      have h := native_re_of_list_cons_ne d ds
      rw [impl_native_re_of_list.eq_2,
        native_re_concat_char_eq c (impl_native_re_of_list (d :: ds)) h.1 h.2]
      simp

theorem native_re_deriv_re_of_list_cons
    (x c : SmtValue) (cs : List SmtValue) :
    native_re_deriv x (impl_native_re_of_list (c :: cs)) =
      if x = c then impl_native_re_of_list cs else SmtRegLan.empty := by
  cases cs with
  | nil =>
      simp [impl_native_re_of_list, native_re_concat, native_re_deriv]
  | cons d ds =>
      have h := native_re_of_list_cons_ne d ds
      rw [impl_native_re_of_list.eq_2,
        native_re_concat_char_eq c (impl_native_re_of_list (d :: ds)) h.1 h.2]
      by_cases hx : x = c <;>
        simp [native_re_deriv, native_re_nullable, native_re_concat,
          native_re_union, hx, h.1]

theorem native_re_nullable_re_of_list (pat : List SmtValue) :
    native_re_nullable (impl_native_re_of_list pat) = decide (pat = []) := by
  cases pat with
  | nil => simp [impl_native_re_of_list, native_re_nullable]
  | cons c cs =>
      cases cs with
      | nil => simp [impl_native_re_of_list, native_re_concat, native_re_nullable]
      | cons d ds =>
          have ht := native_re_of_list_cons_ne d ds
          rw [impl_native_re_of_list.eq_2,
            native_re_concat_char_eq c (impl_native_re_of_list (d :: ds)) ht.1 ht.2]
          simp [native_re_nullable]

theorem native_re_prefix_go_empty (xs : List SmtValue) (n : Nat) :
    impl_native_re_prefix_match_len_go SmtRegLan.empty xs n = none := by
  induction xs generalizing n with
  | nil => simp [impl_native_re_prefix_match_len_go, native_re_nullable]
  | cons x xs ih =>
      rw [impl_native_re_prefix_match_len_go.eq_2]
      simp [native_re_nullable, native_re_deriv, ih]

theorem native_re_prefix_go_re_of_list :
    ∀ (pat xs : List SmtValue) (n : Nat),
      impl_native_re_prefix_match_len_go (impl_native_re_of_list pat) xs n =
        if native_seq_prefix_eq pat xs then some (n + pat.length) else none
  | [], xs, n => by
      cases xs <;>
        simp [impl_native_re_prefix_match_len_go, impl_native_re_of_list,
          native_re_nullable, native_seq_prefix_eq]
  | c :: cs, [], n => by
      rw [impl_native_re_prefix_match_len_go.eq_1]
      simp [native_re_nullable_re_of_list, native_seq_prefix_eq]
  | c :: cs, x :: xs, n => by
      rw [impl_native_re_prefix_match_len_go.eq_2]
      rw [native_re_nullable_re_of_list]
      simp only [List.cons_ne_nil, decide_false, Bool.false_eq_true, if_false]
      rw [native_re_deriv_re_of_list_cons]
      by_cases hx : x = c
      · subst x
        rw [if_pos rfl]
        rw [native_re_prefix_go_re_of_list cs xs (n + 1)]
        by_cases hp : native_seq_prefix_eq cs xs = true
        · simp [native_seq_prefix_eq, native_veq, hp]
          omega
        · simp [native_seq_prefix_eq, native_veq, hp]
      · rw [if_neg hx]
        have hcx : c ≠ x := Ne.symm hx
        simp [native_re_prefix_go_empty, native_seq_prefix_eq, native_veq,
          hcx]

theorem native_re_prefix_match_re_of_list
    (pat xs : List SmtValue) :
    native_re_prefix_match_len? (impl_native_re_of_list pat) xs =
      if native_seq_prefix_eq pat xs then some pat.length else none := by
  simp [native_re_prefix_match_len?, native_re_prefix_go_re_of_list]

theorem native_seq_prefix_eq_length_le :
    ∀ (pat xs : List SmtValue),
      native_seq_prefix_eq pat xs = true → pat.length ≤ xs.length
  | [], xs, h => by simp
  | p :: ps, [], h => by simp [native_seq_prefix_eq] at h
  | p :: ps, x :: xs, h => by
      have hParts : p = x ∧ native_seq_prefix_eq ps xs = true := by
        simpa [native_seq_prefix_eq, native_veq] using h
      simpa using native_seq_prefix_eq_length_le ps xs hParts.2

theorem native_re_find_idx_aux_re_of_list_value :
    ∀ (pat xs : List SmtValue) (i : Nat),
      (match impl_native_re_find_idx_aux (impl_native_re_of_list pat) xs i with
       | some (idx, _) => Int.ofNat idx
       | none => -1) =
        if _h : pat.length ≤ xs.length then
          native_seq_indexof_rec xs pat i (xs.length - pat.length + 1)
        else
          -1
  | pat, [], i => by
      cases pat with
      | nil =>
          simp [impl_native_re_find_idx_aux, native_re_prefix_match_re_of_list,
            native_seq_prefix_eq, native_seq_indexof_rec]
      | cons p ps =>
          simp [impl_native_re_find_idx_aux, native_re_prefix_match_re_of_list,
            native_seq_prefix_eq]
  | pat, x :: xs, i => by
      rw [impl_native_re_find_idx_aux.eq_def, native_re_prefix_match_re_of_list]
      by_cases hp : native_seq_prefix_eq pat (x :: xs) = true
      · rw [if_pos hp]
        have hLen : pat.length ≤ (x :: xs).length :=
          native_seq_prefix_eq_length_le pat (x :: xs) hp
        rw [dif_pos hLen]
        have hFuelPos : 0 < (x :: xs).length - pat.length + 1 := by omega
        obtain ⟨fuel, hFuel⟩ := Nat.exists_eq_succ_of_ne_zero
          (Nat.ne_of_gt hFuelPos)
        rw [hFuel]
        simp [native_seq_indexof_rec, hp]
      · rw [if_neg hp]
        rw [native_re_find_idx_aux_re_of_list_value pat xs (i + 1)]
        by_cases hTail : pat.length ≤ xs.length
        · have hFull : pat.length ≤ (x :: xs).length := by
            simpa using Nat.le.step hTail
          rw [dif_pos hTail, dif_pos hFull]
          have hFuel :
              (x :: xs).length - pat.length + 1 =
                (xs.length - pat.length + 1) + 1 := by
            simp
            omega
          rw [hFuel]
          simp [native_seq_indexof_rec, hp]
        · rw [dif_neg hTail]
          by_cases hFull : pat.length ≤ (x :: xs).length
          · rw [dif_pos hFull]
            have hEq : pat.length = (x :: xs).length := by
              have hGt : xs.length < pat.length := Nat.lt_of_not_ge hTail
              simp only [List.length_cons] at hFull ⊢
              omega
            have hFuel : (x :: xs).length - pat.length + 1 = 1 := by
              omega
            rw [hFuel]
            simp [native_seq_indexof_rec, hp]
          · rw [dif_neg hFull]

theorem native_seq_indexof_eq_rec
    (xs pat : List SmtValue) (i : native_Int) :
    native_seq_indexof xs pat i =
      if i < 0 then
        -1
      else if _h : Int.toNat i + pat.length ≤ xs.length then
        native_seq_indexof_rec (xs.drop (Int.toNat i)) pat (Int.toNat i)
          (xs.length - (Int.toNat i + pat.length) + 1)
      else
        -1 := by
  unfold native_seq_indexof native_str_indexof_re native_str_to_re
  by_cases hi : i < 0
  · simp [hi]
  · simp only [if_neg hi]
    by_cases hStart : Int.toNat i ≤ xs.length
    · rw [if_pos hStart]
      unfold native_re_find_idx_from
      refine (native_re_find_idx_aux_re_of_list_value pat
        (xs.drop (Int.toNat i)) (Int.toNat i)).trans ?_
      by_cases hBounds : Int.toNat i + pat.length ≤ xs.length
      · have hTail : pat.length ≤ (xs.drop (Int.toNat i)).length := by
          rw [List.length_drop]
          omega
        rw [dif_pos hBounds, dif_pos hTail]
        congr 1
        rw [List.length_drop]
        omega
      · have hTail : ¬ pat.length ≤ (xs.drop (Int.toNat i)).length := by
          rw [List.length_drop]
          omega
        rw [dif_neg hBounds, dif_neg hTail]
    · have hBounds : ¬ Int.toNat i + pat.length ≤ xs.length := by
        omega
      rw [if_neg hStart, dif_neg hBounds]

/-- Compatibility form for proofs that expose the regex-backed implementation
of `native_seq_indexof`. -/
@[simp] theorem native_str_indexof_re_to_re_eq_rec
    (xs pat : List SmtValue) (i : native_Int) :
    native_str_indexof_re xs (native_str_to_re pat) i =
      if i < 0 then
        -1
      else if _h : Int.toNat i + pat.length ≤ xs.length then
        native_seq_indexof_rec (xs.drop (Int.toNat i)) pat (Int.toNat i)
          (xs.length - (Int.toNat i + pat.length) + 1)
      else
        -1 := by
  simpa only [native_seq_indexof] using native_seq_indexof_eq_rec xs pat i

theorem native_seq_indexof_rec_eq_neg_one_or_ge
    (xs pat : List SmtValue) :
    (i fuel : Nat) ->
    native_seq_indexof_rec xs pat i fuel = -1 ∨
      Int.ofNat i ≤ native_seq_indexof_rec xs pat i fuel
  | i, 0 => by
      simp [native_seq_indexof_rec]
  | i, fuel + 1 => by
      unfold native_seq_indexof_rec
      split
      · right
        simp
      · cases xs with
        | nil =>
            simp
        | cons _ xs =>
            cases native_seq_indexof_rec_eq_neg_one_or_ge xs pat (i + 1) fuel with
            | inl h =>
                left
                exact h
            | inr h =>
                right
                exact Int.le_trans (Int.ofNat_le.mpr (Nat.le_succ i)) h

theorem native_seq_indexof_eq_neg_one_or_ge
    (xs pat : List SmtValue) (i : native_Int) :
    native_seq_indexof xs pat i = -1 ∨ i ≤ native_seq_indexof xs pat i := by
  rw [native_seq_indexof_eq_rec]
  by_cases hi : i < 0
  · simp [hi]
  · have hi0 : 0 ≤ i := int_nonneg_of_not_neg hi
    simp [hi]
    by_cases hBounds : Int.toNat i + pat.length ≤ xs.length
    · simp [hBounds]
      cases native_seq_indexof_rec_eq_neg_one_or_ge (xs.drop (Int.toNat i)) pat
          (Int.toNat i) (xs.length - (Int.toNat i + pat.length) + 1) with
      | inl h =>
          exact Or.inl h
      | inr h =>
          right
          calc
            i = (Int.toNat i : Int) := (Int.toNat_of_nonneg hi0).symm
            _ ≤ native_seq_indexof_rec (xs.drop (Int.toNat i)) pat (Int.toNat i)
                (xs.length - (Int.toNat i + pat.length) + 1) := h
    · simp [hBounds]

theorem native_seq_indexof_rec_bound
    (xs pat : List SmtValue) :
    (i fuel : Nat) ->
    native_seq_indexof_rec xs pat i fuel = -1 ∨
      ∃ j : Nat, native_seq_indexof_rec xs pat i fuel = Int.ofNat (i + j) ∧
        j < fuel
  | i, 0 => by
      simp [native_seq_indexof_rec]
  | i, fuel + 1 => by
      unfold native_seq_indexof_rec
      split
      · right
        exact ⟨0, by simp, by omega⟩
      · cases xs with
        | nil =>
            simp
        | cons _ xs =>
            cases native_seq_indexof_rec_bound xs pat (i + 1) fuel with
            | inl h =>
                left
                exact h
            | inr h =>
                rcases h with ⟨j, hj, hjlt⟩
                right
                refine ⟨j + 1, ?_, by omega⟩
                simp [hj, Nat.add_comm, Nat.add_left_comm]

theorem native_seq_indexof_le_len
    (xs pat : List SmtValue) (i : native_Int) :
    native_seq_indexof xs pat i ≤ Int.ofNat xs.length := by
  rw [native_seq_indexof_eq_rec]
  split
  · exact Int.le_trans (by decide : (-1 : Int) ≤ 0) (Int.natCast_nonneg _)
  · dsimp
    split
    · rename_i hStart h
      cases native_seq_indexof_rec_bound (xs.drop (Int.toNat i)) pat (Int.toNat i)
          (xs.length - (Int.toNat i + pat.length) + 1) with
      | inl hRec =>
          rw [hRec]
          exact Int.le_trans (by decide : (-1 : Int) ≤ 0) (Int.natCast_nonneg _)
      | inr hRec =>
          rcases hRec with ⟨j, hRec, hjlt⟩
          rw [hRec]
          apply Int.ofNat_le.mpr
          have hjle : j ≤ xs.length - (Int.toNat i + pat.length) := by
            omega
          omega
    · exact Int.le_trans (by decide : (-1 : Int) ≤ 0) (Int.natCast_nonneg _)

theorem native_seq_extract_zero_nat
    (xs : List SmtValue) (n : Nat) (hle : n <= xs.length) :
    native_seq_extract xs 0 (Int.ofNat n) = xs.take n := by
  unfold native_seq_extract
  by_cases hn : n = 0
  · subst n
    simp
  · have hnPosNat : 0 < n := Nat.pos_of_ne_zero hn
    have hnPos : (0 : Int) < Int.ofNat n := Int.ofNat_lt.mpr hnPosNat
    have hxsPosNat : 0 < xs.length := Nat.lt_of_lt_of_le hnPosNat hle
    have hxsNe : xs ≠ [] := by
      intro h
      subst xs
      simp at hxsPosNat
    have hmin : min (Int.ofNat n) (Int.ofNat xs.length) = Int.ofNat n :=
      Int.min_eq_left (Int.ofNat_le.mpr hle)
    have hminToNat :
        (min (Int.ofNat n) (Int.ofNat xs.length)).toNat = n := by
      rw [hmin]
      simp
    have hminNat : min n xs.length = n := Nat.min_eq_left hle
    simp [hn, hxsNe]
    change
      min ((min (Int.ofNat n) (Int.ofNat xs.length)).toNat) xs.length =
        min n xs.length
    rw [hminToNat, hminNat]

theorem native_seq_extract_empty_of_len_nonpos
    (xs : List SmtValue) (i n : native_Int) (h : n ≤ 0) :
    native_seq_extract xs i n = [] := by
  unfold native_seq_extract
  rw [if_pos (by
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inl (Or.inr h))]

theorem native_seq_extract_eq_drop_take
    (xs : List SmtValue) (i n : native_Int)
    (hi : 0 ≤ i) (hn : 0 < n) :
    native_seq_extract xs i n =
      (xs.drop (Int.toNat i)).take (Int.toNat n) := by
  unfold native_seq_extract
  by_cases hOob : Int.ofNat xs.length ≤ i
  · rw [if_pos (by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inr hOob)]
    have hDrop : xs.drop (Int.toNat i) = [] := by
      apply List.drop_eq_nil_of_le
      apply Int.ofNat_le.mp
      rw [Int.toNat_of_nonneg hi]
      exact hOob
    rw [hDrop]
    simp
  · have hiLt : i < Int.ofNat xs.length := Int.lt_of_not_ge hOob
    rw [if_neg (by
      intro hGuard
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hGuard
      rcases hGuard with (hneg | hnLe) | hLenLe
      · exact (Int.not_lt_of_ge hi hneg)
      · exact (Int.not_le_of_gt hn hnLe)
      · exact (Int.not_le_of_gt hiLt hLenLe))]
    by_cases hnLe : n ≤ Int.ofNat xs.length - i
    · rw [Int.min_eq_left hnLe]
    · have hRemLt : Int.ofNat xs.length - i < n :=
        Int.lt_of_not_ge hnLe
      rw [Int.min_eq_right (Int.le_of_lt hRemLt)]
      apply List.take_eq_take_iff.mpr
      have hiNat : Int.toNat i ≤ xs.length := by
        apply Int.ofNat_le.mp
        rw [Int.toNat_of_nonneg hi]
        exact Int.le_of_lt hiLt
      have hDropLen : (xs.drop (Int.toNat i)).length =
          xs.length - Int.toNat i := List.length_drop
      have hRemCast :
          Int.toNat (Int.ofNat xs.length - i) =
            xs.length - Int.toNat i := by
        rw [← Int.toNat_of_nonneg hi]
        exact Int.toNat_sub xs.length (Int.toNat i)
      rw [hDropLen, hRemCast]
      have hRemNatLe : xs.length - Int.toNat i ≤ Int.toNat n := by
        apply Int.ofNat_le.mp
        rw [← hRemCast, Int.toNat_of_nonneg
          (Int.sub_nonneg.mpr (Int.le_of_lt hiLt)),
          Int.toNat_of_nonneg (Int.le_of_lt hn)]
        exact Int.le_of_lt hRemLt
      simp [hRemNatLe]

theorem native_seq_extract_zero_eq_take
    (xs : List SmtValue) (n : native_Int) (hn : 0 ≤ n) :
    native_seq_extract xs 0 n = xs.take (Int.toNat n) := by
  by_cases hZero : n = 0
  · subst n
    simp [native_seq_extract]
  · have hPos : 0 < n := Int.lt_of_not_ge (by
      intro hLe
      exact hZero (Int.le_antisymm hLe hn))
    simpa using
      native_seq_extract_eq_drop_take xs 0 n (by decide) hPos

theorem native_seq_extract_to_end_nat
    (xs : List SmtValue) (i : Nat) (hle : i <= xs.length) :
    native_seq_extract xs (Int.ofNat i) (Int.ofNat (xs.length - i)) =
      xs.drop i := by
  unfold native_seq_extract
  by_cases hend : xs.length - i = 0
  · have hLenLe : xs.length <= i := by omega
    have hcast : (Int.ofNat i >= Int.ofNat xs.length) = true := by
      simp [hLenLe]
    simp [hend, List.drop_eq_nil_of_le hLenLe]
  · have htailPosNat : 0 < xs.length - i := Nat.pos_of_ne_zero hend
    have hiltNat : i < xs.length := by omega
    have htailPos : (0 : Int) < Int.ofNat (xs.length - i) :=
      Int.ofNat_lt.mpr htailPosNat
    have hilt : Int.ofNat i < Int.ofNat xs.length :=
      Int.ofNat_lt.mpr hiltNat
    have hcastSub : Int.ofNat (xs.length - i) = Int.ofNat xs.length - Int.ofNat i :=
      Int.ofNat_sub hle
    have hmin :
        min (Int.ofNat (xs.length - i))
            (Int.ofNat xs.length - Int.ofNat i) =
          Int.ofNat (xs.length - i) := by
      rw [← hcastSub]
      exact Int.min_eq_left (Int.le_refl _)
    have htake :
        (xs.drop i).take (xs.length - i) = xs.drop i := by
      apply List.take_of_length_le
      rw [List.length_drop]
      exact Nat.le_refl _
    have hLenNotLe : ¬ xs.length <= i := Nat.not_le_of_gt hiltNat
    have hiNonneg : ¬ ((i : native_Int) < (0 : native_Int)) := by
      exact Int.not_lt_of_ge (Int.natCast_nonneg i)
    have hminToNat :
        (min (Int.ofNat (xs.length - i))
            (Int.ofNat xs.length - Int.ofNat i)).toNat =
          xs.length - i := by
      rw [hmin]
      simp
    simp [hend, hLenNotLe]
    rw [if_neg hiNonneg]
    change
      List.take
          ((min (Int.ofNat (xs.length - i))
              (Int.ofNat xs.length - Int.ofNat i)).toNat)
          (List.drop i xs) =
        List.drop i xs
    rw [hminToNat]
    exact htake

theorem native_seq_extract_len_tail_of_bounds
    (xs : List SmtValue) (i : native_Int)
    (hNonneg : 0 ≤ i)
    (hLeLen : i ≤ native_seq_len xs) :
    native_seq_extract xs i (native_seq_len xs) =
      xs.drop (Int.toNat i) := by
  have hNotNeg : ¬ i < 0 := Int.not_lt_of_ge hNonneg
  have hToNat : (Int.toNat i : Int) = i :=
    Int.toNat_of_nonneg hNonneg
  have hStartLeInt : (Int.toNat i : Int) ≤ (xs.length : Int) := by
    simpa [hToNat, native_seq_len] using hLeLen
  have hStartLeNat : Int.toNat i ≤ xs.length :=
    Int.ofNat_le.mp hStartLeInt
  by_cases hAtEnd : Int.toNat i = xs.length
  · have hIGeLen : i ≥ (Int.ofNat xs.length : Int) := by
      rw [← hToNat]
      exact Int.ofNat_le.mpr (by omega)
    have hDrop : xs.drop (Int.toNat i) = [] := by
      rw [hAtEnd]
      exact List.drop_eq_nil_of_le (Nat.le_refl _)
    unfold native_seq_extract
    simp [native_seq_len, hNotNeg, hIGeLen, hDrop]
  · have hStartLtNat : Int.toNat i < xs.length :=
      Nat.lt_of_le_of_ne hStartLeNat hAtEnd
    have hINotGeLen : ¬ i ≥ (Int.ofNat xs.length : Int) := by
      intro hGe
      have hGeInt :
          (Int.ofNat xs.length : Int) ≤ (Int.toNat i : Int) := by
        simpa [hToNat] using hGe
      have hGeNat : xs.length ≤ Int.toNat i := Int.ofNat_le.mp hGeInt
      omega
    have hLenNotLeI : ¬ (Int.ofNat xs.length : Int) ≤ i := hINotGeLen
    have hXsNe : xs ≠ [] := by
      intro hNil
      subst xs
      simp at hStartLtNat
    have hLenNotLeZero : ¬ (Int.ofNat xs.length : Int) ≤ 0 := by
      intro hLe
      have hLeNat : xs.length ≤ 0 := Int.ofNat_le.mp hLe
      omega
    have hTailCast :
        Int.ofNat xs.length - i =
          Int.ofNat (xs.length - Int.toNat i) := by
      rw [← hToNat]
      exact (Int.ofNat_sub hStartLeNat).symm
    have hMin :
        min (Int.ofNat xs.length) (Int.ofNat xs.length - i) =
          Int.ofNat xs.length - i := by
      apply Int.min_eq_right
      omega
    unfold native_seq_extract
    simp [native_seq_len, hNotNeg, hLenNotLeZero, hINotGeLen, hXsNe]
    by_cases hLenLeI : (↑xs.length : native_Int) ≤ i
    · exact False.elim (hLenNotLeI (by simpa using hLenLeI))
    · simp [hLenLeI]
      change
        (xs.drop (Int.toNat i)).take
            ((min (Int.ofNat xs.length) (Int.ofNat xs.length - i)).toNat) =
          xs.drop (Int.toNat i)
      rw [hMin, hTailCast]
      apply List.take_of_length_le
      rw [List.length_drop]
      simp

theorem native_seq_prefix_eq_append_drop
    (pat xs : List SmtValue) :
    native_seq_prefix_eq pat xs = true ->
      pat ++ xs.drop pat.length = xs := by
  induction pat generalizing xs with
  | nil =>
      intro _h
      simp
  | cons p ps ih =>
      cases xs with
      | nil =>
          intro h
          simp [native_seq_prefix_eq] at h
      | cons x xs =>
          intro h
          have hParts : p = x ∧ native_seq_prefix_eq ps xs = true := by
            simpa [native_seq_prefix_eq, native_veq] using h
          rcases hParts with ⟨rfl, hTail⟩
          simpa using ih xs hTail

theorem native_seq_prefix_eq_self
    (xs : List SmtValue) :
    native_seq_prefix_eq xs xs = true := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp [native_seq_prefix_eq, native_veq, ih]

@[simp] theorem native_seq_indexof_self_zero
    (xs : List SmtValue) :
    native_seq_indexof xs xs 0 = 0 := by
  rw [native_seq_indexof_eq_rec]
  have hBounds : xs.length ≤ xs.length := Nat.le_refl _
  simp
  unfold native_seq_indexof_rec
  simp [native_seq_prefix_eq_self]

theorem native_seq_contains_self
    (xs : List SmtValue) :
    native_seq_contains xs xs = true := by
  simp [native_seq_contains, native_seq_indexof_self_zero]

theorem native_seq_indexof_rec_decomp
    (xs pat : List SmtValue) :
    (i fuel j : Nat) ->
      native_seq_indexof_rec xs pat i fuel = Int.ofNat j ->
      i ≤ j ∧
        ∃ before after : List SmtValue,
          xs = before ++ pat ++ after ∧ before.length = j - i
  | i, 0, j, h => by
      simp [native_seq_indexof_rec] at h
  | i, fuel + 1, j, h => by
      unfold native_seq_indexof_rec at h
      by_cases hPrefix : native_seq_prefix_eq pat xs = true
      · rw [if_pos hPrefix] at h
        have hji : j = i := Int.ofNat.inj h.symm
        subst j
        constructor
        · exact Nat.le_refl _
        · refine ⟨[], xs.drop pat.length, ?_, by simp⟩
          exact (native_seq_prefix_eq_append_drop pat xs hPrefix).symm
      · rw [if_neg hPrefix] at h
        cases xs with
        | nil =>
            simp at h
        | cons x xs =>
            rcases native_seq_indexof_rec_decomp xs pat (i + 1) fuel j h with
              ⟨hLe, before, after, hXs, hBeforeLen⟩
            constructor
            · omega
            · refine ⟨x :: before, after, ?_, ?_⟩
              · simp [hXs, List.append_assoc]
              · simp [hBeforeLen]
                omega

theorem native_seq_indexof_zero_decomp_of_nat
    (xs pat : List SmtValue) (j : Nat)
    (hIdx : native_seq_indexof xs pat 0 = Int.ofNat j) :
    native_seq_extract xs 0 (Int.ofNat j) ++ pat ++
        native_seq_extract xs (Int.ofNat j + Int.ofNat pat.length)
          (Int.ofNat xs.length - (Int.ofNat j + Int.ofNat pat.length)) =
      xs := by
  rw [native_seq_indexof_eq_rec] at hIdx
  by_cases hBounds : pat.length ≤ xs.length
  · simp [hBounds] at hIdx
    rcases native_seq_indexof_rec_decomp xs pat 0
        (xs.length - pat.length + 1) j hIdx with
      ⟨_hLe, before, after, hXs, hBeforeLen⟩
    have hBeforeLen' : before.length = j := by
      simpa using hBeforeLen
    have hJLe : j ≤ xs.length := by
      have hLen := congrArg List.length hXs
      simp [hBeforeLen'] at hLen
      omega
    have hStartLe : j + pat.length ≤ xs.length := by
      have hLen := congrArg List.length hXs
      simp [hBeforeLen'] at hLen
      omega
    have hPre :
        native_seq_extract xs 0 (Int.ofNat j) = before := by
      rw [native_seq_extract_zero_nat xs j hJLe]
      rw [hXs]
      simp [hBeforeLen']
    have hSub :
        Int.ofNat xs.length - (Int.ofNat j + Int.ofNat pat.length) =
          Int.ofNat (xs.length - (j + pat.length)) := by
      have hAdd :
          Int.ofNat j + Int.ofNat pat.length =
            Int.ofNat (j + pat.length) := by
        simp
      rw [hAdd]
      exact (Int.ofNat_sub hStartLe).symm
    have hSuf :
        native_seq_extract xs (Int.ofNat j + Int.ofNat pat.length)
            (Int.ofNat xs.length - (Int.ofNat j + Int.ofNat pat.length)) =
          after := by
      have hAdd :
          Int.ofNat j + Int.ofNat pat.length =
            Int.ofNat (j + pat.length) := by
        simp
      have hSub' :
          Int.ofNat xs.length - Int.ofNat (j + pat.length) =
            Int.ofNat (xs.length - (j + pat.length)) :=
        (Int.ofNat_sub hStartLe).symm
      rw [hAdd, hSub']
      rw [native_seq_extract_to_end_nat xs (j + pat.length) hStartLe]
      rw [hXs]
      rw [← hBeforeLen']
      simp
    rw [hPre, hSuf, hXs]
  · simp [hBounds] at hIdx

theorem native_seq_indexof_zero_decomp
    (xs pat : List SmtValue)
    (hIdxNonneg : 0 ≤ native_seq_indexof xs pat 0) :
    let idx := native_seq_indexof xs pat 0
    native_seq_extract xs 0 idx ++ pat ++
        native_seq_extract xs (idx + Int.ofNat pat.length)
          (Int.ofNat xs.length - (idx + Int.ofNat pat.length)) =
      xs := by
  let idx := native_seq_indexof xs pat 0
  let j := Int.toNat idx
  have hCast : Int.ofNat j = idx := Int.toNat_of_nonneg hIdxNonneg
  have hIdx : native_seq_indexof xs pat 0 = Int.ofNat j := by
    rw [hCast]
  change
    native_seq_extract xs 0 idx ++ pat ++
        native_seq_extract xs (idx + Int.ofNat pat.length)
          (Int.ofNat xs.length - (idx + Int.ofNat pat.length)) =
      xs
  rw [← hCast]
  exact native_seq_indexof_zero_decomp_of_nat xs pat j hIdx

theorem native_seq_extract_prefix_length_of_indexof_nonneg
    (xs pat : List SmtValue)
    (hIdxNonneg : 0 ≤ native_seq_indexof xs pat 0) :
    Int.ofNat (native_seq_extract xs 0 (native_seq_indexof xs pat 0)).length =
      native_seq_indexof xs pat 0 := by
  let idx := native_seq_indexof xs pat 0
  let j := Int.toNat idx
  have hCast : Int.ofNat j = idx := Int.toNat_of_nonneg hIdxNonneg
  have hIdx : native_seq_indexof xs pat 0 = Int.ofNat j := by
    rw [hCast]
  rw [native_seq_indexof_eq_rec] at hIdx
  by_cases hBounds : pat.length ≤ xs.length
  · simp [hBounds] at hIdx
    rcases native_seq_indexof_rec_decomp xs pat 0
        (xs.length - pat.length + 1) j hIdx with
      ⟨_hLe, before, after, hXs, hBeforeLen⟩
    have hBeforeLen' : before.length = j := by
      simpa using hBeforeLen
    have hJLe : j ≤ xs.length := by
      have hLen := congrArg List.length hXs
      simp [hBeforeLen'] at hLen
      omega
    change Int.ofNat (native_seq_extract xs 0 idx).length = idx
    rw [← hCast]
    rw [native_seq_extract_zero_nat xs j hJLe]
    simp [List.length_take, Nat.min_eq_left hJLe]
  · simp [hBounds] at hIdx

/-! ### Stability of a successful search under right append -/

theorem native_seq_prefix_eq_append_of_eq_true
    (pat xs suffix : List SmtValue)
    (hPrefix : native_seq_prefix_eq pat xs = true) :
    native_seq_prefix_eq pat (xs ++ suffix) = true := by
  induction pat generalizing xs with
  | nil =>
      rfl
  | cons p ps ih =>
      cases xs with
      | nil =>
          simp [native_seq_prefix_eq] at hPrefix
      | cons x xs =>
          have hParts :
              p = x ∧ native_seq_prefix_eq ps xs = true := by
            simpa [native_seq_prefix_eq, native_veq] using hPrefix
          rcases hParts with ⟨rfl, hTail⟩
          simp [native_seq_prefix_eq, native_veq, ih xs hTail]

theorem native_seq_prefix_eq_append_of_length_le
    (pat xs suffix : List SmtValue)
    (hLen : pat.length ≤ xs.length) :
    native_seq_prefix_eq pat (xs ++ suffix) =
      native_seq_prefix_eq pat xs := by
  induction pat generalizing xs with
  | nil =>
      rfl
  | cons p ps ih =>
      cases xs with
      | nil =>
          simp at hLen
      | cons x xs =>
          have hTailLen : ps.length ≤ xs.length := by
            simpa using hLen
          simp [native_seq_prefix_eq, ih xs hTailLen]

theorem native_seq_indexof_rec_append_of_nat_result
    (suffix : List SmtValue) :
    ∀ (xs pat : List SmtValue) (i fuel j : Nat),
      native_seq_indexof_rec xs pat i fuel = Int.ofNat j ->
        native_seq_indexof_rec (xs ++ suffix) pat i
            (fuel + suffix.length) =
          Int.ofNat j := by
  intro xs pat i fuel
  induction fuel generalizing xs i with
  | zero =>
      intro j h
      simp [native_seq_indexof_rec] at h
  | succ fuel ih =>
      intro j h
      rw [Nat.succ_add]
      unfold native_seq_indexof_rec at h ⊢
      by_cases hPrefix : native_seq_prefix_eq pat xs = true
      · rw [if_pos hPrefix] at h
        have hPrefixAppend :=
          native_seq_prefix_eq_append_of_eq_true pat xs suffix hPrefix
        rw [if_pos hPrefixAppend]
        exact h
      · rw [if_neg hPrefix] at h
        cases xs with
        | nil =>
            simp at h
        | cons x xs =>
            have hPatLen : pat.length ≤ (x :: xs).length := by
              rcases native_seq_indexof_rec_decomp xs pat (i + 1) fuel j h with
                ⟨_hLe, before, after, hXs, _hBeforeLen⟩
              have hLengths := congrArg List.length hXs
              simp only [List.length_append] at hLengths
              simp only [List.length_cons]
              omega
            have hPrefixAppend :
                ¬ native_seq_prefix_eq pat ((x :: xs) ++ suffix) = true := by
              rw [native_seq_prefix_eq_append_of_length_le
                pat (x :: xs) suffix hPatLen]
              exact hPrefix
            rw [if_neg hPrefixAppend]
            exact ih xs (i + 1) j h

theorem native_seq_indexof_rec_append_of_nonneg
    (xs pat suffix : List SmtValue) (i fuel : Nat)
    (hNonneg : 0 ≤ native_seq_indexof_rec xs pat i fuel) :
    native_seq_indexof_rec (xs ++ suffix) pat i
        (fuel + suffix.length) =
      native_seq_indexof_rec xs pat i fuel := by
  cases hResult : native_seq_indexof_rec xs pat i fuel with
  | ofNat j =>
      exact native_seq_indexof_rec_append_of_nat_result suffix xs pat i fuel j
        hResult
  | negSucc j =>
      rw [hResult] at hNonneg
      simp at hNonneg

theorem list_drop_append_of_le_length
    (xs suffix : List SmtValue) :
    ∀ n : Nat, n ≤ xs.length ->
      (xs ++ suffix).drop n = xs.drop n ++ suffix
  | 0, _h => by simp
  | n + 1, h => by
      cases xs with
      | nil =>
          simp at h
      | cons x xs =>
          simp only [List.cons_append, List.drop_succ_cons]
          exact list_drop_append_of_le_length xs suffix n (by
            simpa using h)

theorem native_seq_indexof_append_of_nonneg
    (xs pat suffix : List SmtValue) (i : native_Int)
    (hNonneg : 0 ≤ native_seq_indexof xs pat i) :
    native_seq_indexof (xs ++ suffix) pat i =
      native_seq_indexof xs pat i := by
  have hStartNonneg : ¬ i < 0 := by
    intro hNeg
    have hResult : native_seq_indexof xs pat i = -1 := by
      rw [native_seq_indexof_eq_rec]
      simp [hNeg]
    rw [hResult] at hNonneg
    simp at hNonneg
  let start := Int.toNat i
  have hBounds : start + pat.length ≤ xs.length := by
    by_cases hBounds : start + pat.length ≤ xs.length
    · exact hBounds
    · have hResult : native_seq_indexof xs pat i = -1 := by
        rw [native_seq_indexof_eq_rec]
        simp [hStartNonneg, start, hBounds]
      rw [hResult] at hNonneg
      simp at hNonneg
  have hStartLe : start ≤ xs.length := by omega
  have hBoundsAppend : start + pat.length ≤ (xs ++ suffix).length := by
    simp only [List.length_append]
    omega
  have hBoundsRaw : Int.toNat i + pat.length ≤ xs.length := by
    simpa [start] using hBounds
  have hBoundsAppendRaw :
      Int.toNat i + pat.length ≤ (xs ++ suffix).length := by
    simpa [start] using hBoundsAppend
  let fuel := xs.length - (start + pat.length) + 1
  have hFuel :
      (xs ++ suffix).length - (start + pat.length) + 1 =
        fuel + suffix.length := by
    simp only [List.length_append]
    dsimp [fuel]
    omega
  have hNonnegRec :
      0 ≤ native_seq_indexof_rec (xs.drop start) pat start fuel := by
    simpa [native_seq_indexof_eq_rec, hStartNonneg, start, fuel, hBoundsRaw]
      using hNonneg
  rw [native_seq_indexof_eq_rec, native_seq_indexof_eq_rec]
  simp only [if_neg hStartNonneg]
  rw [dif_pos hBoundsAppendRaw, dif_pos hBoundsRaw]
  change native_seq_indexof_rec ((xs ++ suffix).drop start) pat start
      ((xs ++ suffix).length - (start + pat.length) + 1) =
    native_seq_indexof_rec (xs.drop start) pat start
      (xs.length - (start + pat.length) + 1)
  rw [list_drop_append_of_le_length xs suffix start hStartLe, hFuel]
  change native_seq_indexof_rec (xs.drop start ++ suffix) pat start
      (fuel + suffix.length) =
    native_seq_indexof_rec (xs.drop start) pat start fuel
  exact native_seq_indexof_rec_append_of_nonneg
    (xs.drop start) pat suffix start fuel hNonnegRec

/-! ### Updating within a left appendend, including its boundary -/

theorem native_seq_update_append_of_fit
    (xs suffix repl : List SmtValue) (i : native_Int)
    (hNonneg : 0 ≤ i)
    (hFit : i + Int.ofNat repl.length ≤ Int.ofNat xs.length) :
    native_seq_update (xs ++ suffix) i repl =
      xs.take (Int.toNat i) ++ repl ++
        xs.drop (Int.toNat i + repl.length) ++ suffix := by
  by_cases hEmpty : repl = []
  · subst repl
    simp only [List.length_nil, Nat.add_zero, List.append_nil,
      List.take_append_drop]
    simp [native_seq_update]
  have hReplPos : 0 < repl.length := List.length_pos_iff.mpr hEmpty
  have hNeg : ¬ i < 0 := Int.not_lt_of_ge hNonneg
  have hIdxCast : Int.ofNat (Int.toNat i) = i :=
    Int.toNat_of_nonneg hNonneg
  have hFitNat : Int.toNat i + repl.length ≤ xs.length := by
    have hFitCast := hFit
    rw [← hIdxCast] at hFitCast
    apply Int.ofNat_le.mp
    simpa using hFitCast
  have hIdxLt : Int.toNat i < xs.length := by omega
  have hIdxLe : Int.toNat i ≤ xs.length := Nat.le_of_lt hIdxLt
  have hReplFits : repl.length ≤ xs.length - Int.toNat i := by omega
  have hReplFitsAppend :
      repl.length ≤ (xs ++ suffix).length - Int.toNat i := by
    simp only [List.length_append]
    omega
  have hBelowAppend : ¬ Int.ofNat (xs ++ suffix).length ≤ i := by
    have hiLtXs : i < Int.ofNat xs.length := by
      rw [← hIdxCast]
      exact Int.ofNat_lt.mpr hIdxLt
    have hXsLeAppend :
        Int.ofNat xs.length ≤ Int.ofNat (xs ++ suffix).length := by
      simp only [List.length_append]
      exact Int.ofNat_le.mpr (Nat.le_add_right _ _)
    exact Int.not_le_of_gt (Int.lt_of_lt_of_le hiLtXs hXsLeAppend)
  unfold native_seq_update
  rw [show decide (i < 0) = false from decide_eq_false hNeg]
  simp only [Bool.false_or]
  rw [show decide (Int.ofNat (xs ++ suffix).length ≤ i) = false from
    decide_eq_false hBelowAppend]
  simp only [Bool.false_eq_true, if_false]
  rw [List.take_append_of_le_length hIdxLe]
  rw [List.take_of_length_le hReplFitsAppend]
  rw [list_drop_append_of_le_length xs suffix
    (Int.toNat i + repl.length) (by omega)]
  simp only [List.append_assoc]

theorem native_seq_update_replace_middle
    (pre old suffix replacement : List SmtValue)
    (hLen : old.length = replacement.length) :
    native_seq_update (pre ++ old ++ suffix) (Int.ofNat pre.length) replacement =
      pre ++ replacement ++ suffix := by
  rw [native_seq_update_append_of_fit (pre ++ old) suffix replacement
    (Int.ofNat pre.length) (Int.natCast_nonneg _) (by simp [List.length_append, hLen])]
  change (pre ++ old).take pre.length ++ replacement ++
    (pre ++ old).drop (pre.length + replacement.length) ++ suffix = _
  rw [← hLen, ← List.length_append, List.drop_length]
  simp

theorem native_seq_update_nil (xs : List SmtValue) (i : Int) :
    native_seq_update xs i [] = xs := by simp [native_seq_update]

theorem native_seq_update_reverse_of_length_le_one (xs ys : List SmtValue) (i : Int)
    (hlen : ys.length ≤ 1) :
    native_seq_update xs.reverse i ys =
      (native_seq_update xs ((xs.length : Int) - (i + 1)) ys).reverse := by
  cases ys with
  | nil => simp [native_seq_update_nil]
  | cons c cs =>
    have hc : cs = [] := by simpa using hlen
    subst cs
    by_cases hneg : i < 0
    · have hj : (xs.length : Int) ≤ (xs.length : Int) - (i + 1) := by omega
      simp [native_seq_update, hneg, hj]
    by_cases hoob : (xs.length : Int) ≤ i
    · have hj : (xs.length : Int) - (i + 1) < 0 := by omega
      simp [native_seq_update, List.length_reverse, hoob, hj]
    have hi : 0 ≤ i := by omega
    have hj : 0 ≤ (xs.length : Int) - (i + 1) := by omega
    have hjlt : (xs.length : Int) - (i + 1) < (xs.length : Int) := by omega
    have hin : i.toNat < xs.length := by omega
    have hjn : ((xs.length : Int) - (i + 1)).toNat = xs.length - (i.toNat + 1) := by omega
    have hremain : 1 ≤ xs.length - i.toNat := by omega
    have hremainj : 1 ≤ xs.length - (xs.length - (i.toNat + 1)) := by omega
    simp only [native_seq_update, List.length_reverse, Int.ofNat_eq_natCast]
    rw [if_neg (by simp [hneg, hoob]), if_neg (by simp [Int.not_lt.mpr hj, Int.not_le.mpr hjlt])]
    simp only [List.length_cons, List.length_nil, Nat.zero_add, hjn]
    rw [List.take_of_length_le (l := [c]) hremain,
      List.take_of_length_le (l := [c]) hremainj]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.take_reverse, List.drop_reverse]
    rw [show xs.length - (i.toNat + 1) + 1 = xs.length - i.toNat by omega]
    simp [List.append_assoc]

theorem native_seq_indexof_of_length_lt
    (xs pat : List SmtValue) (i : Int) (h : xs.length < pat.length) :
    native_seq_indexof xs pat i = -1 := by
  rw [native_seq_indexof_eq_rec]
  have hBounds : ¬ i.toNat + pat.length ≤ xs.length := by omega
  simp [hBounds]
