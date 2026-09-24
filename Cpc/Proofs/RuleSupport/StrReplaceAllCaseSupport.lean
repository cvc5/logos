module

public import Cpc.SmtEval
import all Cpc.SmtEval
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport
public import Cpc.Proofs.RuleSupport.StrContainsReplCharSupport
import all Cpc.Proofs.RuleSupport.StrContainsReplCharSupport
public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport
public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.StrOverlapSupport
import all Cpc.Proofs.RuleSupport.StrOverlapSupport
public import Cpc.Proofs.RuleSupport.StrSubstrContainsSupport
import all Cpc.Proofs.RuleSupport.StrSubstrContainsSupport
public import Cpc.Proofs.RuleSupport.ConcatSplitSupport
import all Cpc.Proofs.RuleSupport.ConcatSplitSupport
public import Cpc.Proofs.Canonical.Pump
import all Cpc.Proofs.Canonical.Pump
public import Cpc.Proofs.RuleSupport.StrReplaceAllSupport
import all Cpc.Proofs.RuleSupport.StrReplaceAllSupport
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

/-!
The `str_replace_all` case of `string_reduction`.

The reduction predicate for `str.replace_all` constrains the
`@strings_num_occur` / `@strings_occur_index` /
`@strings_replace_all_result` skolems.  Their translations evaluate, over a
total typed model, to the greedy-scan data developed in
`StrReplaceAllSupport`: the occurrence count, the scan boundaries (as the
unique witnesses of the `occur_index` choice), and the replace-all results
on boundary suffixes.  This file proves the whole case as
`str_replace_all_reduction_pred_true`, consumed by
`Cpc.Proofs.Rules.String_reduction`.
-/

namespace StrReplaceAllCase

open StrReplaceAllSupport

/-! ### Small evaluation equations -/

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

private theorem eval_neg_term_eq (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.neg x y) =
      __smtx_model_eval__ (__smtx_model_eval M x)
        (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_lt_term_eq (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.lt x y) =
      __smtx_model_eval_lt (__smtx_model_eval M x)
        (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_geq_term_eq (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.geq x y) =
      __smtx_model_eval_geq (__smtx_model_eval M x)
        (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_str_indexof_term_eq (M : SmtModel) (x y z : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_indexof x y z) =
      __smtx_model_eval_str_indexof (__smtx_model_eval M x)
        (__smtx_model_eval M y) (__smtx_model_eval M z) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_str_replace_all_term_eq
    (M : SmtModel) (x y z : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_replace_all x y z) =
      __smtx_model_eval_str_replace_all (__smtx_model_eval M x)
        (__smtx_model_eval M y) (__smtx_model_eval M z) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_choice_term_eq
    (M : SmtModel) (s : native_String) (T : SmtType) (b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.choice s T b) =
      native_eval_choice M s T b := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-! ### Choice determination by a unique witness -/

private theorem tchoice_eq_of_unique
    (M : SmtModel) (s : native_String) (T : SmtType) (b : SmtTerm)
    (v₀ : SmtValue)
    (hTy : __smtx_typeof_value v₀ = T)
    (hCanon : __smtx_value_canonical v₀ = true)
    (hSat : __smtx_model_eval (native_model_push M s T v₀) b =
      SmtValue.Boolean true)
    (hUnique : ∀ v : SmtValue, __smtx_typeof_value v = T ->
      __smtx_value_canonical v = true ->
      __smtx_model_eval (native_model_push M s T v) b =
        SmtValue.Boolean true -> v = v₀) :
    native_eval_choice M s T b = v₀ := by
  classical
  have hEx : ∃ v : SmtValue, __smtx_typeof_value v = T ∧
      __smtx_value_canonical v = true ∧
      __smtx_model_eval (native_model_push M s T v) b =
        SmtValue.Boolean true := ⟨v₀, hTy, hCanon, hSat⟩
  rw [dif_pos hEx]
  rcases Classical.choose_spec hEx with ⟨h1, h2, h3⟩
  exact hUnique _ h1 h2 h3

/-! ### Variable lookups under pushes -/

private theorem var_lookup_push_same
    (M : SmtModel) (s : native_String) (T : SmtType) (v : SmtValue) :
    native_model_var_lookup (native_model_push M s T v) s T = v := by
  simp [native_model_var_lookup, native_model_push]

private theorem var_lookup_push_ne
    (M : SmtModel) (s s' : native_String) (T T' : SmtType) (v : SmtValue)
    (hNe : s' ≠ s) :
    native_model_var_lookup (native_model_push M s T v) s' T' =
      native_model_var_lookup M s' T' := by
  simp [native_model_var_lookup, native_model_push, SmtModelKey.mk.injEq,
    hNe]

private theorem str_index_ne_x :
    native_string_lit "@var.str_index" ≠ native_string_lit "@x" := by
  decide

/-! ### Evaluating the `@strings_num_occur` translation -/

private theorem extract_zero_one (ss : List SmtValue) :
    native_seq_extract ss 0 1 = ss.take 1 := by
  simpa using native_seq_extract_zero_eq_take ss 1 (by decide)

private theorem extract_zero_zero (ss : List SmtValue) :
    native_seq_extract ss 0 0 = ss.take 0 := by
  simpa using native_seq_extract_zero_eq_take ss 0 (by decide)

/-- The value of the `@strings_num_occur` translation: the number of greedy
occurrences, as counted by `occEnds`. -/
private theorem num_occur_eval
    (M' : SmtModel) (S T : SmtTerm) (E : SmtType)
    (ss ts : List SmtValue)
    (hS : __smtx_model_eval M' S = SmtValue.Seq (native_pack_seq E ss))
    (hT : __smtx_model_eval M' T = SmtValue.Seq (native_pack_seq E ts))
    (hTs : ts ≠ []) :
    __smtx_model_eval M'
        (SmtTerm.neg
          (SmtTerm.str_len
            (SmtTerm.str_replace_all S T
              (SmtTerm.str_substr S (SmtTerm.Numeral 0)
                (SmtTerm.Numeral 1))))
          (SmtTerm.str_len
            (SmtTerm.str_replace_all S T
              (SmtTerm.str_substr S (SmtTerm.Numeral 0)
                (SmtTerm.Numeral 0))))) =
      SmtValue.Numeral ((occEnds ts ss).length : Int) := by
  have hDiff := num_occur_int ts ss hTs
  rw [eval_neg_term_eq, smtx_eval_str_len_term_eq, smtx_eval_str_len_term_eq,
    eval_str_replace_all_term_eq, eval_str_replace_all_term_eq,
    StrSubstrContainsSupport.smtx_eval_str_substr_term_eq,
    StrSubstrContainsSupport.smtx_eval_str_substr_term_eq,
    eval_numeral_term_eq, eval_numeral_term_eq, hS, hT]
  simp only [__smtx_model_eval_str_substr, __smtx_model_eval_str_replace_all,
    __smtx_model_eval_str_len, __smtx_model_eval__,
    Smtm.native_unpack_pack_seq, elem_typeof_pack_seq, native_seq_len,
    extract_zero_one, extract_zero_zero, List.take_zero]
  simp only [native_zplus, native_zneg, Int.ofNat_eq_natCast]
  congr 1
  try omega

private theorem eval_and_term_eq (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.and x y) =
      __smtx_model_eval_and (__smtx_model_eval M x)
        (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_or_term_eq (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.or x y) =
      __smtx_model_eval_or (__smtx_model_eval M x)
        (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_eq_term_eq (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.eq x y) =
      __smtx_model_eval_eq (__smtx_model_eval M x)
        (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem numeral_canonical (m : native_Int) :
    __smtx_value_canonical (SmtValue.Numeral m) = true := by
  simp [__smtx_value_canonical]

private theorem numeral_typeof (m : native_Int) :
    __smtx_typeof_value (SmtValue.Numeral m) = SmtType.Int := by
  simp [__smtx_typeof_value]

private theorem extract_zero_toNat (ss : List SmtValue) (m : Int) :
    native_seq_extract ss 0 m = ss.take (Int.toNat m) := by
  by_cases hm : 0 ≤ m
  · exact native_seq_extract_zero_eq_take ss m hm
  · have hm' : m ≤ 0 := by omega
    have hTake : Int.toNat m = 0 := by omega
    rw [hTake]
    unfold native_seq_extract
    rw [if_pos]
    · rfl
    · simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inl (Or.inr hm')

/-! ### The `@strings_occur_index` choice body -/

/-- The choice body of the `@strings_occur_index` translation, with the
count argument `w`. -/
private def oiBody (S T w : SmtTerm) : SmtTerm :=
  let index := SmtTerm.Var (native_string_lit "@x") SmtType.Int
  let pref := SmtTerm.str_substr S (SmtTerm.Numeral 0) index
  let previous := SmtTerm.str_substr S (SmtTerm.Numeral 0)
    (SmtTerm.neg index (SmtTerm.Numeral 1))
  let numOccur := fun source =>
    SmtTerm.neg
      (SmtTerm.str_len
        (SmtTerm.str_replace_all source T
          (SmtTerm.str_substr source (SmtTerm.Numeral 0)
            (SmtTerm.Numeral 1))))
      (SmtTerm.str_len
        (SmtTerm.str_replace_all source T
          (SmtTerm.str_substr source (SmtTerm.Numeral 0)
            (SmtTerm.Numeral 0))))
  SmtTerm.and
    (SmtTerm.geq index (SmtTerm.Numeral 0))
    (SmtTerm.and
      (SmtTerm.eq
        (numOccur pref) w)
      (SmtTerm.or
        (SmtTerm.eq index (SmtTerm.Numeral 0))
        (SmtTerm.lt
          (numOccur previous) w)))

private theorem find_nonempty_aux_str_to_re_cons_eq
    (p : SmtValue) (ps : List SmtValue) :
    ∀ (xs : List SmtValue) (idx : Nat),
      impl_native_re_find_nonempty_idx_aux (native_str_to_re (p :: ps)) xs idx =
        impl_native_re_find_idx_aux (native_str_to_re (p :: ps)) xs idx
  | [], idx => by
      rw [impl_native_re_find_nonempty_idx_aux.eq_def,
        impl_native_re_find_idx_aux.eq_def,
        positive_prefix_str_to_re_cons,
        show native_str_to_re (p :: ps) = impl_native_re_of_list (p :: ps) from rfl,
        native_re_prefix_match_re_of_list]
      simp [native_str_to_re, native_seq_prefix_eq]
  | x :: xs, idx => by
      rw [impl_native_re_find_nonempty_idx_aux.eq_def,
        impl_native_re_find_idx_aux.eq_def,
        positive_prefix_str_to_re_cons,
        show native_str_to_re (p :: ps) = impl_native_re_of_list (p :: ps) from rfl,
        native_re_prefix_match_re_of_list]
      by_cases hPrefix : native_seq_prefix_eq (p :: ps) (x :: xs) = true
      · simp [hPrefix]
      · simp only [if_neg hPrefix]
        exact find_nonempty_aux_str_to_re_cons_eq p ps xs (idx + 1)

private theorem find_nonempty_from_str_to_re_cons_eq
    (p : SmtValue) (ps xs : List SmtValue) (start : Nat) :
    impl_native_re_find_nonempty_idx_from (native_str_to_re (p :: ps)) xs start =
      native_re_find_idx_from (native_str_to_re (p :: ps)) xs start := by
  unfold impl_native_re_find_nonempty_idx_from native_re_find_idx_from
  exact find_nonempty_aux_str_to_re_cons_eq p ps _ _

private theorem find_nonempty_aux_add_offset
    (r : SmtRegLan) :
    ∀ (xs : List SmtValue) (off base : Nat),
      impl_native_re_find_nonempty_idx_aux r xs (base + off) =
        (impl_native_re_find_nonempty_idx_aux r xs off).map
          (fun result => (base + result.1, result.2))
  | [], off, base => by
      simp [impl_native_re_find_nonempty_idx_aux,
        native_re_positive_prefix_match_len?]
  | x :: xs, off, base => by
      rw [impl_native_re_find_nonempty_idx_aux.eq_def,
        impl_native_re_find_nonempty_idx_aux.eq_def]
      cases hPrefix : native_re_positive_prefix_match_len? r (x :: xs) with
      | none =>
          simp only [hPrefix]
          simpa [Nat.add_assoc] using
            find_nonempty_aux_add_offset r xs (off + 1) base
      | some n =>
          cases n with
          | zero =>
              simp only [hPrefix]
              simpa [Nat.add_assoc] using
                find_nonempty_aux_add_offset r xs (off + 1) base
          | succ n => simp [hPrefix]

private theorem find_nonempty_from_shift
    (r : SmtRegLan) (xs : List SmtValue) (start : Nat) :
    impl_native_re_find_nonempty_idx_from r xs start =
      (impl_native_re_find_nonempty_idx_from r (xs.drop start) 0).map
        (fun result => (start + result.1, result.2)) := by
  unfold impl_native_re_find_nonempty_idx_from
  simpa using find_nonempty_aux_add_offset r (xs.drop start) 0 start

private theorem scan_ends_aux_str_to_re_cons_eq
    (p : SmtValue) (ps xs : List SmtValue) :
    ∀ (fuel pos : Nat), pos ≤ xs.length →
      impl_native_re_scan_ends_aux fuel (native_str_to_re (p :: ps)) xs pos =
        (occEndsAux fuel (p :: ps) (xs.drop pos)).map
          (fun endPos => pos + endPos)
  | 0, pos, hPos => by
      simp [impl_native_re_scan_ends_aux, occEndsAux]
  | fuel + 1, pos, hPos => by
      rw [impl_native_re_scan_ends_aux, occEndsAux_succ,
        find_nonempty_from_shift,
        find_nonempty_from_str_to_re_cons_eq]
      cases hFind : native_re_find_idx_from
          (native_str_to_re (p :: ps)) (xs.drop pos) 0 with
      | none =>
          have hIndex : native_seq_indexof (xs.drop pos) (p :: ps) 0 = -1 := by
            simp [native_seq_indexof, native_str_indexof_re, hFind]
          simp [hFind, hIndex]
      | some result =>
          rcases result with ⟨idx, matchLen⟩
          simp only [hFind, Option.map_some]
          have hMatchLen : matchLen = (p :: ps).length := by
            apply StrEqReplSupport.native_re_find_idx_aux_re_of_list_length
              (p :: ps) (xs.drop pos) 0 idx matchLen
            simpa [native_re_find_idx_from, native_str_to_re] using hFind
          have hIndex :
              native_seq_indexof (xs.drop pos) (p :: ps) 0 = Int.ofNat idx := by
            simp [native_seq_indexof, native_str_indexof_re, hFind]
          have hBounds : idx + (p :: ps).length ≤ (xs.drop pos).length := by
            have h := StrEqReplSupport.native_seq_indexof_zero_bounds_of_nonneg
              (xs.drop pos) (p :: ps) (by rw [hIndex]; exact Int.natCast_nonneg _)
            simpa [hIndex] using h
          have hNext : pos + idx + matchLen ≤ xs.length := by
            rw [hMatchLen]
            rw [List.length_drop] at hBounds
            omega
          rw [scan_ends_aux_str_to_re_cons_eq p ps xs fuel
            (pos + idx + matchLen) hNext]
          rw [hIndex]
          rw [if_neg (show ¬ Int.ofNat idx < 0 from
            Int.not_lt_of_ge (Int.natCast_nonneg idx))]
          simp [hFind, hMatchLen, List.drop_drop, List.map_map,
            Function.comp_def, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem occ_ends_aux_eq (fuel : Nat) (pat xs : List SmtValue) :
    impl_native_re_scan_ends_aux fuel (native_str_to_re pat) xs 0 =
      occEndsAux fuel pat xs := by
  cases pat with
  | nil =>
      have hEpsilon : ∀ (ys : List SmtValue) (idx : Nat),
          impl_native_re_find_nonempty_idx_aux SmtRegLan.epsilon ys idx = none := by
        intro ys
        induction ys with
        | nil =>
            intro idx
            simp [impl_native_re_find_nonempty_idx_aux,
              native_re_positive_prefix_match_len?]
        | cons y ys ih =>
            intro idx
            rw [impl_native_re_find_nonempty_idx_aux.eq_def]
            simp [native_re_positive_prefix_match_len?, native_re_deriv,
              native_re_prefix_match_len?, native_re_prefix_go_empty, ih]
      have hFind : impl_native_re_find_nonempty_idx_from
          (native_str_to_re []) xs 0 = none := by
        simpa [impl_native_re_find_nonempty_idx_from, native_str_to_re,
          impl_native_re_of_list] using hEpsilon xs 0
      cases fuel <;> simp [impl_native_re_scan_ends_aux, occEndsAux, hFind]
  | cons p ps =>
      simpa using scan_ends_aux_str_to_re_cons_eq p ps xs fuel 0 (by omega)

/-- The native scan-boundary function agrees with `bound` in range. -/
private theorem occ_index_eq_bound (ss ts : List SmtValue) (nn : Nat)
    (hnn : nn ≤ (occEnds ts ss).length) :
    native_seq_occur_index ss ts ((nn : Nat) : Int) =
      ((bound ts ss nn : Nat) : Int) := by
  have hAux : impl_native_re_scan_ends_aux (ss.length + 1)
      (native_str_to_re ts) ss 0 =
      occEnds ts ss := occ_ends_aux_eq (ss.length + 1) ts ss
  simp only [native_seq_occur_index, native_str_occur_index_re, hAux]
  rw [if_pos]
  · rw [Int.toNat_natCast]
    simp only [bound, Int.ofNat_eq_natCast]
  · refine ⟨Int.natCast_nonneg _, ?_⟩
    rw [Int.toNat_natCast]
    simp only [List.length_cons]
    omega

private theorem oi_term_eq (M : SmtModel) (S T w : SmtTerm) :
    __smtx_model_eval M (SmtTerm._at_strings_occur_index S T w) =
      __smtx_model_eval__at_strings_occur_index (__smtx_model_eval M S)
        (__smtx_model_eval M T) (__smtx_model_eval M w) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- Truth of the `occur_index` choice body over concrete values. -/
private theorem oi_body_eval_true_iff
    (N : SmtModel) (S T w : SmtTerm) (E : SmtType)
    (ss ts : List SmtValue) (nn : Nat) (m : Int)
    (hS : __smtx_model_eval N S = SmtValue.Seq (native_pack_seq E ss))
    (hT : __smtx_model_eval N T = SmtValue.Seq (native_pack_seq E ts))
    (hW : __smtx_model_eval N w = SmtValue.Numeral (nn : Int))
    (hXv : native_model_var_lookup N (native_string_lit "@x") SmtType.Int =
      SmtValue.Numeral m)
    (hTs : ts ≠ []) :
    (__smtx_model_eval N (oiBody S T w) = SmtValue.Boolean true) ↔
      (0 ≤ m ∧
        ((occEnds ts (ss.take (Int.toNat m))).length : Int) = (nn : Int) ∧
        (m = 0 ∨
          ((occEnds ts (ss.take (Int.toNat (m - 1)))).length : Int) <
            (nn : Int))) := by
  have hPrefix1 :
      __smtx_model_eval N
          (SmtTerm.str_substr S (SmtTerm.Numeral 0)
            (SmtTerm.Var (native_string_lit "@x") SmtType.Int)) =
        SmtValue.Seq (native_pack_seq E (ss.take (Int.toNat m))) := by
    rw [StrSubstrContainsSupport.smtx_eval_str_substr_term_eq, hS,
      eval_numeral_term_eq, eval_var_term_eq, hXv]
    simp only [__smtx_model_eval_str_substr, Smtm.native_unpack_pack_seq,
      elem_typeof_pack_seq, extract_zero_toNat]
  have hPrefix2 :
      __smtx_model_eval N
          (SmtTerm.str_substr S (SmtTerm.Numeral 0)
            (SmtTerm.neg
              (SmtTerm.Var (native_string_lit "@x") SmtType.Int)
              (SmtTerm.Numeral 1))) =
        SmtValue.Seq (native_pack_seq E (ss.take (Int.toNat (m - 1)))) := by
    rw [StrSubstrContainsSupport.smtx_eval_str_substr_term_eq, hS,
      eval_numeral_term_eq, eval_neg_term_eq, eval_var_term_eq, hXv,
      eval_numeral_term_eq]
    simp only [__smtx_model_eval__, __smtx_model_eval_str_substr,
      Smtm.native_unpack_pack_seq, elem_typeof_pack_seq,
      native_zplus, native_zneg, extract_zero_toNat]
    rw [show m + -1 = m - 1 by omega]
  have hNum1 := num_occur_eval N _ T E (ss.take (Int.toNat m)) ts
    hPrefix1 hT hTs
  have hNum2 := num_occur_eval N _ T E (ss.take (Int.toNat (m - 1))) ts
    hPrefix2 hT hTs
  simp only [oiBody, eval_and_term_eq, eval_or_term_eq, eval_eq_term_eq,
    eval_geq_term_eq, eval_lt_term_eq, eval_var_term_eq,
    eval_numeral_term_eq, hXv, hNum1, hNum2, hW]
  simp only [__smtx_model_eval_and, __smtx_model_eval_or,
    __smtx_model_eval_eq, __smtx_model_eval_geq, __smtx_model_eval_leq,
    __smtx_model_eval_lt, native_and, native_or, native_veq, native_zleq,
    native_zlt]
  constructor
  · intro h
    simp only [SmtValue.Boolean.injEq, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq, SmtValue.Numeral.injEq] at h
    exact h
  · intro h
    simp only [SmtValue.Boolean.injEq, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq, SmtValue.Numeral.injEq]
    exact h

/-- The value of the `@strings_occur_index` term at a count `nn` in
range: the `nn`-th scan boundary. -/
private theorem oi_eval
    (M' : SmtModel) (S T w : SmtTerm) (E : SmtType)
    (ss ts : List SmtValue) (nn : Nat)
    (hS : __smtx_model_eval M' S = SmtValue.Seq (native_pack_seq E ss))
    (hT : __smtx_model_eval M' T = SmtValue.Seq (native_pack_seq E ts))
    (hW : __smtx_model_eval M' w = SmtValue.Numeral (nn : Int))
    (hTs : ts ≠ [])
    (hnn : nn ≤ (occEnds ts ss).length) :
    __smtx_model_eval M' (SmtTerm._at_strings_occur_index S T w) =
      SmtValue.Numeral ((bound ts ss nn : Nat) : Int) := by
  rw [oi_term_eq, hS, hT, hW]
  simp only [__smtx_model_eval__at_strings_occur_index,
    Smtm.native_unpack_pack_seq, elem_typeof_pack_seq]
  rw [occ_index_eq_bound ss ts nn hnn]

private theorem extract_full_drop (ss : List SmtValue) (b : Nat)
    (hb : b ≤ ss.length) :
    native_seq_extract ss ((b : Nat) : Int) ((ss.length : Nat) : Int) =
      ss.drop b := by
  by_cases hLen : ss.length = 0
  · have hNil : ss = [] := List.eq_nil_of_length_eq_zero hLen
    subst hNil
    simp [native_seq_extract]
  by_cases hEq : b = ss.length
  · subst hEq
    unfold native_seq_extract
    rw [if_pos]
    · rw [List.drop_length]
    · simp only [Bool.or_eq_true, decide_eq_true_eq]
      right
      simp [Int.ofNat_eq_natCast]
  · have hLt : b < ss.length := by omega
    unfold native_seq_extract
    rw [if_neg]
    · rw [Int.toNat_natCast]
      have hMin :
          min ((ss.length : Nat) : Int)
              (Int.ofNat ss.length - ((b : Nat) : Int)) =
            ((ss.length - b : Nat) : Int) := by
        simp only [Int.ofNat_eq_natCast]
        omega
      rw [hMin, Int.toNat_natCast]
      apply List.take_of_length_le
      rw [List.length_drop]
      exact Nat.le_refl _
    · simp only [Bool.or_eq_true, decide_eq_true_eq, Int.ofNat_eq_natCast]
      intro hAbs
      unfold native_Int at hAbs
      rcases hAbs with (h1 | h2) | h3 <;> omega

/-- Typing of the `@strings_occur_index` term. -/
private theorem oi_typeof (S T w : SmtTerm) (E : SmtType)
    (hS : __smtx_typeof S = SmtType.Seq E)
    (hT : __smtx_typeof T = SmtType.Seq E)
    (hW : __smtx_typeof w = SmtType.Int) :
    __smtx_typeof (SmtTerm._at_strings_occur_index S T w) =
      SmtType.Int := by
  have hTy :
      __smtx_typeof (SmtTerm._at_strings_occur_index S T w) =
        __smtx_typeof_str_indexof (__smtx_typeof S) (__smtx_typeof T)
          (__smtx_typeof w) := by
    rw [__smtx_typeof.eq_def] <;> simp only
  rw [hTy, hS, hT, hW]
  simp [__smtx_typeof_str_indexof, native_ite, native_Teq]

/-- The value of the `@strings_replace_all_result` translation: the
replace-all of the suffix at the `nn`-th boundary. -/
private theorem rar_eval
    (M' : SmtModel) (S T R w : SmtTerm) (E : SmtType)
    (ss ts rs : List SmtValue) (nn : Nat)
    (hS : __smtx_model_eval M' S = SmtValue.Seq (native_pack_seq E ss))
    (hT : __smtx_model_eval M' T = SmtValue.Seq (native_pack_seq E ts))
    (hR : __smtx_model_eval M' R = SmtValue.Seq (native_pack_seq E rs))
    (hW : __smtx_model_eval M' w = SmtValue.Numeral (nn : Int))
    (hTs : ts ≠ [])
    (hnn : nn ≤ (occEnds ts ss).length) :
    __smtx_model_eval M'
        (SmtTerm.str_replace_all
          (SmtTerm.str_substr S (SmtTerm._at_strings_occur_index S T w)
            (SmtTerm.str_len S))
          T R) =
      SmtValue.Seq
        (native_pack_seq E
          (native_seq_replace_all (ss.drop (bound ts ss nn)) ts rs)) := by
  have hOi := oi_eval M' S T w E ss ts nn hS hT hW hTs hnn
  rw [eval_str_replace_all_term_eq,
    StrSubstrContainsSupport.smtx_eval_str_substr_term_eq,
    smtx_eval_str_len_term_eq, hS, hT, hR, hOi]
  simp only [__smtx_model_eval_str_len, __smtx_model_eval_str_substr,
    Smtm.native_unpack_pack_seq, elem_typeof_pack_seq, native_seq_len]
  rw [show Int.ofNat ss.length = ((ss.length : Nat) : Int) by
    simp [Int.ofNat_eq_natCast]]
  rw [extract_full_drop ss (bound ts ss nn) (bound_le_len ts ss nn hnn)]
  simp only [__smtx_model_eval_str_replace_all, Smtm.native_unpack_pack_seq,
    elem_typeof_pack_seq]

/-! ### Closedness of the arguments and the `forall` encoding -/

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

private theorem eval_forall_encoding_true
    (M : SmtModel) (s : native_String) (T : SmtType) (body : SmtTerm)
    (hAll :
      ∀ v : SmtValue,
        __smtx_typeof_value v = T ->
        __smtx_value_canonical v = true ->
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

private theorem extract_cast_drop_take (ss : List SmtValue) (a b : Nat) :
    native_seq_extract ss ((a : Nat) : Int) ((b : Nat) : Int) =
      (ss.drop a).take b := by
  by_cases hb : b = 0
  · subst hb
    unfold native_seq_extract
    rw [if_pos]
    · simp
    · simp only [Bool.or_eq_true, decide_eq_true_eq]
      left
      right
      simp
  · rw [native_seq_extract_eq_drop_take ss _ _ (Int.natCast_nonneg a)
      (by exact_mod_cast Nat.pos_of_ne_zero hb)]
    simp [Int.toNat_natCast]

private theorem int_wf : __smtx_type_wf SmtType.Int = true := by
  simp [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
    native_and]

/-- The choice value at a well-formed type is always typed and canonical
(local copy of the `SkolemizeSupport` fact, kept off that import chain). -/
private theorem tchoice_typed_canonical_of_wf'
    (N : SmtModel) (s : native_String) (T : SmtType) (body : SmtTerm)
    (hWf : __smtx_type_wf T = true) :
    __smtx_typeof_value (native_eval_choice N s T body) = T ∧
      __smtx_value_canonical (native_eval_choice N s T body) =
        true := by
  classical
  by_cases hSat :
      ∃ v : SmtValue,
        __smtx_typeof_value v = T ∧
          __smtx_value_canonical v = true ∧
          __smtx_model_eval (native_model_push N s T v) body =
            SmtValue.Boolean true
  · rw [dif_pos hSat]
    exact ⟨(Classical.choose_spec hSat).1, (Classical.choose_spec hSat).2.1⟩
  · have hTy : ∃ v : SmtValue,
        __smtx_typeof_value v = T ∧ __smtx_value_canonical v := by
      rcases canonical_type_inhabited_of_type_wf T hWf with ⟨v, hvTy, hvCan⟩
      exact ⟨v, hvTy, by simpa [value_canonical] using hvCan⟩
    rw [dif_neg hSat, dif_pos hTy]
    refine ⟨(Classical.choose_spec hTy).1, ?_⟩
    simpa using (Classical.choose_spec hTy).2

private theorem agrees_push_push
    (M : SmtModel) (s₁ : native_String) (T₁ : SmtType) (v₁ : SmtValue)
    (s₂ : native_String) (T₂ : SmtType) (v₂ : SmtValue) :
    model_agrees_on_globals M
      (native_model_push (native_model_push M s₁ T₁ v₁) s₂ T₂ v₂) := by
  refine ⟨?_, ?_⟩
  · intro s' T'
    simp [native_model_lookup, model_key, native_model_push]
  · intro fid A B
    simp [model_fun_lookup, model_key, native_model_push]

/-! ### The `str_replace_all` case -/

set_option maxHeartbeats 40000000 in
/-- The `str_replace_all` case of `string_reduction_pred_true`. -/
theorem str_replace_all_reduction_pred_true
    (M : SmtModel) (hM : model_wf M) (z y x : Term)
    (hTrans : RuleProofs.eo_has_smt_translation
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_all) z) y) x))
    (hClosed : __eo_is_closed
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_all) z) y)
          x) =
      Term.Boolean true) :
    eo_interprets M
      (__str_reduction_pred
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_all) z) y)
          x)) true := by
  let tz := __eo_to_smt z
  let ty := __eo_to_smt y
  let tx := __eo_to_smt x
  have hOrigNN :
      term_has_non_none_type (SmtTerm.str_replace_all tz ty tx) := by
    have hsimpa := hTrans
    try simp [tz, ty, tx, RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace_all)
      (typeof_str_replace_all_eq tz ty tx) hOrigNN with
    ⟨T, hzTy, hyTy, hxTy⟩
  have hZNN : term_has_non_none_type tz := by
    unfold term_has_non_none_type
    rw [hzTy]
    exact seq_ne_none T
  have hYNN : term_has_non_none_type ty := by
    unfold term_has_non_none_type
    rw [hyTy]
    exact seq_ne_none T
  have hXNN : term_has_non_none_type tx := by
    unfold term_has_non_none_type
    rw [hxTy]
    exact seq_ne_none T
  have hZTermNe : z ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation z (by
      have hsimpa := hZNN; (try simp [tz, RuleProofs.eo_has_smt_translation] at hsimpa ⊢); exact hsimpa)
  have hYTermNe : y ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y (by
      have hsimpa := hYNN; (try simp [ty, RuleProofs.eo_has_smt_translation] at hsimpa ⊢); exact hsimpa)
  have hXTermNe : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x (by
      have hsimpa := hXNN; (try simp [tx, RuleProofs.eo_has_smt_translation] at hsimpa ⊢); exact hsimpa)
  have hTWf : __smtx_type_wf T = true :=
    (smt_seq_component_wf_of_non_none_type tz T hzTy).2
  have hTInh : type_inhabited T :=
    (smt_seq_component_wf_of_non_none_type tz T hzTy).1
  have hClosedArgs :
      __eo_is_closed z = Term.Boolean true ∧
        __eo_is_closed y = Term.Boolean true ∧
          __eo_is_closed x = Term.Boolean true := by
    apply eo_is_closed_ternary_uop_args UserOp.str_replace_all z y x
    · decide
    · decide
    · exact hZTermNe
    · exact hYTermNe
    · exact hXTermNe
    · exact hClosed
  -- the SMT-side components of the translated predicate
  let idxName := native_string_lit "@var.str_index"
  let idx := SmtTerm.Var idxName SmtType.Int
  let numOcc :=
    SmtTerm.neg
      (SmtTerm.str_len
        (SmtTerm.str_replace_all tz ty
          (SmtTerm.str_substr tz (SmtTerm.Numeral 0)
            (SmtTerm.Numeral 1))))
      (SmtTerm.str_len
        (SmtTerm.str_replace_all tz ty
          (SmtTerm.str_substr tz (SmtTerm.Numeral 0)
            (SmtTerm.Numeral 0))))
  let startI := SmtTerm.str_indexof tz ty
    (SmtTerm._at_strings_occur_index tz ty idx)
  let iNext := SmtTerm.plus idx
    (SmtTerm.plus (SmtTerm.Numeral 1) (SmtTerm.Numeral 0))
  let seg := SmtTerm.str_substr tz
    (SmtTerm._at_strings_occur_index tz ty idx)
    (SmtTerm.neg startI (SmtTerm._at_strings_occur_index tz ty idx))
  let sourceLen := SmtTerm.str_len tz
  let result := SmtTerm._at_purify (SmtTerm.str_replace_all tz ty tx)
  -- the EO segment term whose element type seeds the `nil` of the
  -- concatenation list
  let idxEO := Term.Var (Term.String (native_string_lit "@var.str_index"))
    (Term.UOp UserOp.Int)
  let oiEO := Term.Apply
    (Term.Apply
      (Term.Apply (Term.UOp UserOp._at_strings_occur_index) z) y) idxEO
  let startEO := Term.Apply
    (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) z) y) oiEO
  let segEO := Term.Apply
    (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) z) oiEO)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg) startEO) oiEO)
  let nilSegS := __eo_to_smt
    (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof segEO))
  let emptyS := __eo_to_smt (__seq_empty (__eo_typeof z))
  -- typing of the components
  have hIdxTy : __smtx_typeof idx = SmtType.Int := by
    dsimp [idx]
    rw [__smtx_typeof.eq_def] <;>
      simp [__smtx_typeof_guard_wf, native_ite, __smtx_type_wf,
        __smtx_type_wf_component, __smtx_type_wf_rec, native_and]
  have hNumTy : ∀ k : native_Int,
      __smtx_typeof (SmtTerm.Numeral k) = SmtType.Int := by
    intro k
    rw [__smtx_typeof.eq_def] <;> simp only
  have hNumOccTy : __smtx_typeof numOcc = SmtType.Int := by
    dsimp [numOcc]
    simp [typeof_neg_eq, typeof_str_len_eq, typeof_str_replace_all_eq,
      typeof_str_substr_eq, hNumTy, hzTy, hyTy,
      __smtx_typeof_str_substr, __smtx_typeof_seq_op_3,
      __smtx_typeof_seq_op_1_ret, __smtx_typeof_arith_overload_op_2,
      native_ite, native_Teq]
  have hOiTy : ∀ w : SmtTerm, __smtx_typeof w = SmtType.Int ->
      __smtx_typeof (SmtTerm._at_strings_occur_index tz ty w) =
        SmtType.Int := by
    intro w hw
    exact oi_typeof tz ty w T hzTy hyTy hw
  have hOiIdxTy := hOiTy idx hIdxTy
  have hOiNumOccTy := hOiTy numOcc hNumOccTy
  have hOiZeroTy := hOiTy (SmtTerm.Numeral 0) (hNumTy 0)
  have hINextTy : __smtx_typeof iNext = SmtType.Int := by
    dsimp [iNext]
    simp [typeof_plus_eq, hIdxTy, hNumTy,
      __smtx_typeof_arith_overload_op_2, native_ite, native_Teq]
  have hOiINextTy := hOiTy iNext hINextTy
  have hStartITy : __smtx_typeof startI = SmtType.Int := by
    dsimp [startI]
    rw [typeof_str_indexof_eq, hzTy, hyTy, hOiIdxTy]
    simp [__smtx_typeof_str_indexof, native_ite, native_Teq]
  have hSegTy : __smtx_typeof seg = SmtType.Seq T := by
    dsimp [seg]
    rw [typeof_str_substr_eq, hzTy, hOiIdxTy, typeof_neg_eq, hStartITy,
      hOiIdxTy]
    simp [__smtx_typeof_str_substr, __smtx_typeof_arith_overload_op_2]
  have hSegEoTy : __smtx_typeof (__eo_to_smt segEO) = SmtType.Seq T := by
    exact hSegTy
  have hSourceLenTy : __smtx_typeof sourceLen = SmtType.Int := by
    dsimp [sourceLen]
    rw [typeof_str_len_eq, hzTy]
    simp [__smtx_typeof_seq_op_1_ret]
  have hResultTy : __smtx_typeof result = SmtType.Seq T := by
    change __smtx_typeof (SmtTerm.str_replace_all tz ty tx) = SmtType.Seq T
    rw [typeof_str_replace_all_eq, hzTy, hyTy, hxTy]
    simp [__smtx_typeof_seq_op_3, native_ite, native_Teq]
  have hRarTy : ∀ w : SmtTerm, __smtx_typeof w = SmtType.Int ->
      __smtx_typeof
          (SmtTerm.str_replace_all
            (SmtTerm.str_substr tz
              (SmtTerm._at_strings_occur_index tz ty w) sourceLen)
            ty tx) = SmtType.Seq T := by
    intro w hw
    rw [typeof_str_replace_all_eq, typeof_str_substr_eq, hzTy,
      hOiTy w hw, hSourceLenTy, hyTy, hxTy]
    simp [__smtx_typeof_str_substr, __smtx_typeof_seq_op_3, native_ite,
      native_Teq]
  have hNilSegNe :
      __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof segEO) ≠
        Term.Stuck :=
    nil_str_concat_typeof_ne_stuck_of_smt_type_seq segEO T hSegEoTy
  have hEmptyNe : __seq_empty (__eo_typeof z) ≠ Term.Stuck :=
    seq_empty_typeof_ne_stuck_of_smt_type_seq z T
      (by simpa [tz] using hzTy)
  have hNilSegTy : __smtx_typeof nilSegS = SmtType.Seq T := by
    simpa [nilSegS] using
      smt_typeof_nil_str_concat_typeof_of_smt_type_seq segEO T hSegEoTy
  have hEmptyNN : term_has_non_none_type emptyS := by
    have hsimpa :=
      seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf
        z T (by simpa [tz] using hzTy) hTInh hTWf
    try simp [emptyS, tz] at hsimpa ⊢
    exact hsimpa
  have hEmptyTy : __smtx_typeof emptyS = SmtType.Seq T := by
    simpa [emptyS, tz] using
      smt_typeof_seq_empty_typeof z T (by simpa [tz] using hzTy) hEmptyNN
  -- the translated reduction predicate
  let rarT : SmtTerm -> SmtTerm := fun w =>
    SmtTerm.str_replace_all
      (SmtTerm.str_substr tz (SmtTerm._at_strings_occur_index tz ty w)
        sourceLen)
      ty tx
  let qBody := SmtTerm.or
    (SmtTerm.not (SmtTerm.geq idx (SmtTerm.Numeral 0)))
    (SmtTerm.or (SmtTerm.not (SmtTerm.lt idx numOcc))
      (SmtTerm.or
        (SmtTerm.and
          (SmtTerm.not (SmtTerm.eq startI (SmtTerm.Numeral (-1))))
          (SmtTerm.and
            (SmtTerm.eq (rarT idx)
              (SmtTerm.str_concat seg
                (SmtTerm.str_concat tx
                  (SmtTerm.str_concat (rarT iNext) nilSegS))))
            (SmtTerm.and
              (SmtTerm.eq (SmtTerm._at_strings_occur_index tz ty iNext)
                (SmtTerm.plus startI
                  (SmtTerm.plus (SmtTerm.str_len ty) (SmtTerm.Numeral 0))))
              (SmtTerm.Boolean true))))
        (SmtTerm.Boolean false)))
  let forallPart := SmtTerm.not
    (SmtTerm.exists idxName SmtType.Int (SmtTerm.not qBody))
  let formula := SmtTerm.ite (SmtTerm.eq ty emptyS)
    (SmtTerm.eq result tz)
    (SmtTerm.and (SmtTerm.geq numOcc (SmtTerm.Numeral 0))
      (SmtTerm.and (SmtTerm.eq result (rarT (SmtTerm.Numeral 0)))
        (SmtTerm.and
          (SmtTerm.eq (rarT numOcc)
            (SmtTerm.str_substr tz
              (SmtTerm._at_strings_occur_index tz ty numOcc) sourceLen))
          (SmtTerm.and
            (SmtTerm.eq (SmtTerm._at_strings_occur_index tz ty
              (SmtTerm.Numeral 0)) (SmtTerm.Numeral 0))
            (SmtTerm.and
              (SmtTerm.eq
                (SmtTerm.str_indexof tz ty
                  (SmtTerm._at_strings_occur_index tz ty numOcc))
                (SmtTerm.Numeral (-1)))
              (SmtTerm.and forallPart (SmtTerm.Boolean true)))))))
  have hNilSegNe' :
      __eo_nil (Term.UOp UserOp.str_concat)
          (__eo_typeof
            (Term.Apply
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) z)
                (Term.Apply
                  (Term.Apply
                    (Term.Apply
                      (Term.UOp UserOp._at_strings_occur_index) z) y)
                  (Term.Var
                    (Term.String (native_string_lit "@var.str_index"))
                    (Term.UOp UserOp.Int))))
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.neg)
                  (Term.Apply
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.str_indexof) z) y)
                    (Term.Apply
                      (Term.Apply
                        (Term.Apply
                          (Term.UOp UserOp._at_strings_occur_index) z) y)
                      (Term.Var
                        (Term.String (native_string_lit "@var.str_index"))
                        (Term.UOp UserOp.Int)))))
                (Term.Apply
                  (Term.Apply
                    (Term.Apply
                      (Term.UOp UserOp._at_strings_occur_index) z) y)
                  (Term.Var
                    (Term.String (native_string_lit "@var.str_index"))
                    (Term.UOp UserOp.Int)))))) ≠
        Term.Stuck := by
    simpa only [segEO, oiEO, startEO, idxEO] using hNilSegNe
  have hFormulaEq :
      __eo_to_smt
          (__str_reduction_pred
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_replace_all) z) y) x)) =
        formula := by
    simp only [__str_reduction_pred, __eo_mk_apply, hZTermNe, hYTermNe,
      hXTermNe, hNilSegNe', hEmptyNe]
    rfl
  have hRar0Ty : __smtx_typeof (rarT (SmtTerm.Numeral 0)) =
      SmtType.Seq T := hRarTy (SmtTerm.Numeral 0) (hNumTy 0)
  have hRarIdxTy : __smtx_typeof (rarT idx) = SmtType.Seq T :=
    hRarTy idx hIdxTy
  have hRarINextTy : __smtx_typeof (rarT iNext) = SmtType.Seq T :=
    hRarTy iNext hINextTy
  have hRarNumTy : __smtx_typeof (rarT numOcc) = SmtType.Seq T :=
    hRarTy numOcc hNumOccTy
  have hSubstrNumTy :
      __smtx_typeof
          (SmtTerm.str_substr tz
            (SmtTerm._at_strings_occur_index tz ty numOcc) sourceLen) =
        SmtType.Seq T := by
    rw [typeof_str_substr_eq, hzTy, hOiNumOccTy, hSourceLenTy]
    simp [__smtx_typeof_str_substr]
  have hIndexofNumTy :
      __smtx_typeof
          (SmtTerm.str_indexof tz ty
            (SmtTerm._at_strings_occur_index tz ty numOcc)) =
        SmtType.Int := by
    rw [typeof_str_indexof_eq, hzTy, hyTy, hOiNumOccTy]
    simp [__smtx_typeof_str_indexof, native_ite, native_Teq]
  have hLenYTy : __smtx_typeof (SmtTerm.str_len ty) = SmtType.Int := by
    rw [typeof_str_len_eq, hyTy]
    simp [__smtx_typeof_seq_op_1_ret]
  have hConcatTy :
      __smtx_typeof
          (SmtTerm.str_concat seg
            (SmtTerm.str_concat tx
              (SmtTerm.str_concat (rarT iNext) nilSegS))) =
        SmtType.Seq T := by
    simp [typeof_str_concat_eq, hSegTy, hxTy, hRarINextTy, hNilSegTy,
      __smtx_typeof_seq_op_2, native_ite, native_Teq]
  have hPlusTy :
      __smtx_typeof
          (SmtTerm.plus startI
            (SmtTerm.plus (SmtTerm.str_len ty) (SmtTerm.Numeral 0))) =
        SmtType.Int := by
    simp [typeof_plus_eq, hStartITy, hLenYTy, hNumTy,
      __smtx_typeof_arith_overload_op_2]
  have hBoolTy : ∀ b : native_Bool,
      __smtx_typeof (SmtTerm.Boolean b) = SmtType.Bool := by
    intro b
    rw [__smtx_typeof.eq_def] <;> simp only
  have hQBodyTy : __smtx_typeof qBody = SmtType.Bool := by
    simp [qBody, hBoolTy, typeof_or_eq, typeof_and_eq, typeof_not_eq, typeof_eq_eq,
      typeof_geq_eq, typeof_lt_eq, hIdxTy, hNumTy, hNumOccTy, hStartITy,
      hRarIdxTy, hConcatTy, hOiINextTy, hPlusTy, __smtx_typeof_eq,
      __smtx_typeof_guard, __smtx_typeof_arith_overload_op_2_ret,
      native_ite, native_Teq, native_and]
  apply RuleProofs.eo_interprets_of_bool_eval M _ true
  · unfold RuleProofs.eo_has_bool_type
    rw [hFormulaEq]
    simp [formula, forallPart, typeof_ite_eq, typeof_and_eq, typeof_eq_eq,
      typeof_geq_eq, typeof_not_eq, smtx_typeof_exists_term_eq,
      hEmptyTy, hyTy, hResultTy, hzTy, hRar0Ty, hRarNumTy, hSubstrNumTy,
      hOiZeroTy, hNumTy, hIndexofNumTy, hNumOccTy, hQBodyTy, hBoolTy,
      __smtx_typeof_eq, __smtx_typeof_guard, __smtx_typeof_guard_wf,
      __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_ite,
      __smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
      native_ite, native_Teq, native_and]
  · rw [hFormulaEq]
    have hZValTy :
        __smtx_typeof_value (__smtx_model_eval M tz) = SmtType.Seq T := by
      simpa [tz, hzTy] using
        smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt z) hZNN
    have hYValTy :
        __smtx_typeof_value (__smtx_model_eval M ty) = SmtType.Seq T := by
      simpa [ty, hyTy] using
        smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt y) hYNN
    have hXValTy :
        __smtx_typeof_value (__smtx_model_eval M tx) = SmtType.Seq T := by
      simpa [tx, hxTy] using
        smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x) hXNN
    rcases seq_value_canonical hZValTy with ⟨sz, hZEval⟩
    rcases seq_value_canonical hYValTy with ⟨sy, hYEval⟩
    rcases seq_value_canonical hXValTy with ⟨sx, hXEval⟩
    have hSzTy : __smtx_typeof_seq_value sz = SmtType.Seq T := by
      simpa [hZEval, __smtx_typeof_value] using hZValTy
    have hSyTy : __smtx_typeof_seq_value sy = SmtType.Seq T := by
      simpa [hYEval, __smtx_typeof_value] using hYValTy
    have hSxTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
      simpa [hXEval, __smtx_typeof_value] using hXValTy
    have hElemZ : __smtx_elem_typeof_seq_value sz = T :=
      elem_typeof_seq_value_of_typeof_seq_value hSzTy
    have hElemY : __smtx_elem_typeof_seq_value sy = T :=
      elem_typeof_seq_value_of_typeof_seq_value hSyTy
    have hElemX : __smtx_elem_typeof_seq_value sx = T :=
      elem_typeof_seq_value_of_typeof_seq_value hSxTy
    let zs := native_unpack_seq sz
    let ys := native_unpack_seq sy
    let rs := native_unpack_seq sx
    have hZPack : native_pack_seq T zs = sz := by
      simpa [zs, hElemZ] using native_pack_unpack_seq sz
    have hYPack : native_pack_seq T ys = sy := by
      simpa [ys, hElemY] using native_pack_unpack_seq sy
    have hXPack : native_pack_seq T rs = sx := by
      simpa [rs, hElemX] using native_pack_unpack_seq sx
    have hZEval' :
        __smtx_model_eval M tz = SmtValue.Seq (native_pack_seq T zs) := by
      rw [hZEval, hZPack]
    have hYEval' :
        __smtx_model_eval M ty = SmtValue.Seq (native_pack_seq T ys) := by
      rw [hYEval, hYPack]
    have hXEval' :
        __smtx_model_eval M tx = SmtValue.Seq (native_pack_seq T rs) := by
      rw [hXEval, hXPack]
    have hSyEmptyIff : sy = SmtSeq.empty T ↔ ys = [] := by
      constructor
      · intro hEmpty
        dsimp [ys]
        rw [hEmpty]
        rfl
      · intro hEmpty
        rw [← hYPack, hEmpty]
        rfl
    have hEmptyEval :
        __smtx_model_eval M emptyS = SmtValue.Seq (SmtSeq.empty T) := by
      simpa [emptyS, tz] using
        eval_seq_empty_typeof M z T (by simpa [tz] using hzTy)
    have hZAt : ∀ N : SmtModel, model_agrees_on_globals M N ->
        __smtx_model_eval N tz = SmtValue.Seq (native_pack_seq T zs) := by
      intro N hAgree
      rw [← hZEval']
      exact (smt_model_eval_eq_of_eo_closed z hClosedArgs.1 M N hAgree).symm
    have hYAt : ∀ N : SmtModel, model_agrees_on_globals M N ->
        __smtx_model_eval N ty = SmtValue.Seq (native_pack_seq T ys) := by
      intro N hAgree
      rw [← hYEval']
      exact
        (smt_model_eval_eq_of_eo_closed y hClosedArgs.2.1 M N hAgree).symm
    have hXAt : ∀ N : SmtModel, model_agrees_on_globals M N ->
        __smtx_model_eval N tx = SmtValue.Seq (native_pack_seq T rs) := by
      intro N hAgree
      rw [← hXEval']
      exact
        (smt_model_eval_eq_of_eo_closed x hClosedArgs.2.2 M N hAgree).symm
    rw [smtx_eval_ite_term_eq]
    by_cases hYs : ys = []
    · -- empty pattern: `replace_all` is the identity
      have hSy : sy = SmtSeq.empty T := hSyEmptyIff.mpr hYs
      have hCond :
          __smtx_model_eval M (SmtTerm.eq ty emptyS) =
            SmtValue.Boolean true := by
        rw [eval_eq_term_eq, hYEval, hEmptyEval, hSy]
        simp [__smtx_model_eval_eq, veq_refl_true]
      rw [hCond]
      simp only [__smtx_model_eval_ite]
      rw [eval_eq_term_eq, eval_purify_term_eq,
        eval_str_replace_all_term_eq, hZEval', hYEval', hXEval']
      simp [__smtx_model_eval_str_replace_all, __smtx_model_eval__at_purify,
        Smtm.native_unpack_pack_seq, elem_typeof_pack_seq, hYs,
        replace_all_nil_pat, __smtx_model_eval_eq, veq_refl_true]
    · -- nonempty pattern: the greedy scan facts
      have hSyNe : sy ≠ SmtSeq.empty T := fun h => hYs (hSyEmptyIff.mp h)
      have hCond :
          __smtx_model_eval M (SmtTerm.eq ty emptyS) =
            SmtValue.Boolean false := by
        rw [eval_eq_term_eq, hYEval, hEmptyEval]
        have hne : SmtValue.Seq sy ≠ SmtValue.Seq (SmtSeq.empty T) := by
          intro h
          injection h with h'
          exact hSyNe h'
        have hveqF :
            native_veq (SmtValue.Seq sy)
                (SmtValue.Seq (SmtSeq.empty T)) = false := by
          cases hb : native_veq (SmtValue.Seq sy)
              (SmtValue.Seq (SmtSeq.empty T)) with
          | true => exact absurd (eq_of_native_veq_true hb) hne
          | false => rfl
        simp [__smtx_model_eval_eq, hveqF]
      rw [hCond]
      simp only [__smtx_model_eval_ite]
      -- shared evaluation facts
      have hNumOccM :
          __smtx_model_eval M numOcc =
            SmtValue.Numeral ((occEnds ys zs).length : Int) :=
        num_occur_eval M tz ty T zs ys hZEval' hYEval' hYs
      have hZPush : ∀ v : SmtValue,
          __smtx_model_eval
              (native_model_push M (native_string_lit "@x") SmtType.Int v)
              tz = SmtValue.Seq (native_pack_seq T zs) := fun v =>
        hZAt _ (model_agrees_on_globals_push M _ _ v)
      have hYPush : ∀ v : SmtValue,
          __smtx_model_eval
              (native_model_push M (native_string_lit "@x") SmtType.Int v)
              ty = SmtValue.Seq (native_pack_seq T ys) := fun v =>
        hYAt _ (model_agrees_on_globals_push M _ _ v)
      have hXPush : ∀ v : SmtValue,
          __smtx_model_eval
              (native_model_push M (native_string_lit "@x") SmtType.Int v)
              tx = SmtValue.Seq (native_pack_seq T rs) := fun v =>
        hXAt _ (model_agrees_on_globals_push M _ _ v)
      have hNumPush : ∀ v : SmtValue,
          __smtx_model_eval
              (native_model_push M (native_string_lit "@x") SmtType.Int v)
              numOcc =
            SmtValue.Numeral (((occEnds ys zs).length : Nat) : Int) :=
        fun v => num_occur_eval _ tz ty T zs ys (hZPush v) (hYPush v) hYs
      have hZeroPush : ∀ v : SmtValue,
          __smtx_model_eval
              (native_model_push M (native_string_lit "@x") SmtType.Int v)
              (SmtTerm.Numeral 0) =
            SmtValue.Numeral (((0 : Nat) : Nat) : Int) := by
        intro v
        rw [eval_numeral_term_eq]
        norm_cast
      -- conjunct 1: the count is nonnegative
      have hC1 :
          __smtx_model_eval M (SmtTerm.geq numOcc (SmtTerm.Numeral 0)) =
            SmtValue.Boolean true := by
        rw [eval_geq_term_eq, hNumOccM, eval_numeral_term_eq]
        simp only [__smtx_model_eval_geq, __smtx_model_eval_leq,
          native_zleq, SmtValue.Boolean.injEq, decide_eq_true_eq]
        exact Int.natCast_nonneg _
      -- conjunct 2: the purified original equals `rar 0`
      have hResultEval :
          __smtx_model_eval M result =
            SmtValue.Seq
              (native_pack_seq T (native_seq_replace_all zs ys rs)) := by
        simp only [result]
        rw [eval_purify_term_eq, eval_str_replace_all_term_eq, hZEval',
          hYEval', hXEval']
        simp [__smtx_model_eval_str_replace_all,
          __smtx_model_eval__at_purify, Smtm.native_unpack_pack_seq,
          elem_typeof_pack_seq]
      have hRar0Eval :
          __smtx_model_eval M (rarT (SmtTerm.Numeral 0)) =
            SmtValue.Seq
              (native_pack_seq T
                (native_seq_replace_all
                  (zs.drop (bound ys zs 0)) ys rs)) := by
        simp only [rarT, sourceLen]
        exact rar_eval M tz ty tx (SmtTerm.Numeral 0) T zs ys rs 0
          hZEval' hYEval' hXEval'
          (by
            rw [eval_numeral_term_eq]
            norm_cast)
          hYs (Nat.zero_le _)
      have hC2 :
          __smtx_model_eval M
              (SmtTerm.eq result (rarT (SmtTerm.Numeral 0))) =
            SmtValue.Boolean true := by
        rw [eval_eq_term_eq, hResultEval, hRar0Eval, bound_zero,
          List.drop_zero]
        simp [__smtx_model_eval_eq, veq_refl_true]
      -- conjunct 3: `rar` at the count is the untouched tail
      have hOiKM :
          __smtx_model_eval M
              (SmtTerm._at_strings_occur_index tz ty numOcc) =
            SmtValue.Numeral
              ((bound ys zs (occEnds ys zs).length : Nat) : Int) :=
        oi_eval M tz ty numOcc T zs ys (occEnds ys zs).length
          hZEval' hYEval' hNumOccM hYs (Nat.le_refl _)
      have hRarKEval :
          __smtx_model_eval M (rarT numOcc) =
            SmtValue.Seq
              (native_pack_seq T
                (native_seq_replace_all
                  (zs.drop (bound ys zs (occEnds ys zs).length)) ys
                  rs)) := by
        simp only [rarT, sourceLen]
        exact rar_eval M tz ty tx numOcc T zs ys rs
          (occEnds ys zs).length hZEval' hYEval' hXEval'
          hNumOccM hYs (Nat.le_refl _)
      have hSubstrKEval :
          __smtx_model_eval M
              (SmtTerm.str_substr tz
                (SmtTerm._at_strings_occur_index tz ty numOcc)
                sourceLen) =
            SmtValue.Seq
              (native_pack_seq T
                (zs.drop (bound ys zs (occEnds ys zs).length))) := by
        simp only [sourceLen]
        rw [StrSubstrContainsSupport.smtx_eval_str_substr_term_eq,
          smtx_eval_str_len_term_eq, hZEval', hOiKM]
        simp only [__smtx_model_eval_str_len, __smtx_model_eval_str_substr,
          Smtm.native_unpack_pack_seq, elem_typeof_pack_seq, native_seq_len]
        rw [show Int.ofNat zs.length = ((zs.length : Nat) : Int) by
          simp [Int.ofNat_eq_natCast]]
        rw [extract_full_drop zs _
          (bound_le_len ys zs _ (Nat.le_refl _))]
      have hC3 :
          __smtx_model_eval M
              (SmtTerm.eq (rarT numOcc)
                (SmtTerm.str_substr tz
                  (SmtTerm._at_strings_occur_index tz ty numOcc)
                  sourceLen)) = SmtValue.Boolean true := by
        rw [eval_eq_term_eq, hRarKEval, hSubstrKEval,
          replace_all_drop_bound_last ys rs zs hYs]
        simp [__smtx_model_eval_eq, veq_refl_true]
      -- conjunct 4: the zeroth boundary is zero
      have hOi0M :
          __smtx_model_eval M
              (SmtTerm._at_strings_occur_index tz ty (SmtTerm.Numeral 0)) =
            SmtValue.Numeral ((bound ys zs 0 : Nat) : Int) :=
        oi_eval M tz ty (SmtTerm.Numeral 0) T zs ys 0 hZEval' hYEval'
          (by
            rw [eval_numeral_term_eq]
            norm_cast)
          hYs (Nat.zero_le _)
      have hC4 :
          __smtx_model_eval M
              (SmtTerm.eq
                (SmtTerm._at_strings_occur_index tz ty (SmtTerm.Numeral 0))
                (SmtTerm.Numeral 0)) = SmtValue.Boolean true := by
        rw [eval_eq_term_eq, hOi0M, eval_numeral_term_eq, bound_zero]
        simp [__smtx_model_eval_eq, native_veq]
      -- conjunct 5: no occurrence after the last boundary
      have hC5 :
          __smtx_model_eval M
              (SmtTerm.eq
                (SmtTerm.str_indexof tz ty
                  (SmtTerm._at_strings_occur_index tz ty numOcc))
                (SmtTerm.Numeral (-1))) = SmtValue.Boolean true := by
        rw [eval_eq_term_eq, eval_str_indexof_term_eq, hZEval', hYEval',
          hOiKM, eval_numeral_term_eq]
        simp only [__smtx_model_eval_str_indexof,
          Smtm.native_unpack_pack_seq, elem_typeof_pack_seq]
        rw [indexof_at_bound_last ys zs hYs]
        simp [__smtx_model_eval_eq, veq_refl_true]
      -- conjunct 6: the recurrence for every index value
      have hC6 : __smtx_model_eval M forallPart = SmtValue.Boolean true := by
        simp only [forallPart]
        apply eval_forall_encoding_true
        intro v hvTy hvCan
        rcases int_value_canonical hvTy with ⟨m, rfl⟩
        have hAgreeMk := model_agrees_on_globals_push M idxName
          SmtType.Int (SmtValue.Numeral m)
        have hZMk := hZAt _ hAgreeMk
        have hYMk := hYAt _ hAgreeMk
        have hXMk := hXAt _ hAgreeMk
        have hIdxMk :
            __smtx_model_eval
                (native_model_push M idxName SmtType.Int
                  (SmtValue.Numeral m)) idx = SmtValue.Numeral m := by
          simp only [idx]
          rw [eval_var_term_eq]
          exact var_lookup_push_same M idxName SmtType.Int _
        have hNumOccMk := num_occur_eval
          (native_model_push M idxName SmtType.Int (SmtValue.Numeral m))
          tz ty T zs ys hZMk hYMk hYs
        have hZMkPush : ∀ v : SmtValue,
            __smtx_model_eval
                (native_model_push
                  (native_model_push M idxName SmtType.Int
                    (SmtValue.Numeral m))
                  (native_string_lit "@x") SmtType.Int v) tz =
              SmtValue.Seq (native_pack_seq T zs) := fun v =>
          hZAt _ (agrees_push_push M idxName SmtType.Int
            (SmtValue.Numeral m) _ _ v)
        have hYMkPush : ∀ v : SmtValue,
            __smtx_model_eval
                (native_model_push
                  (native_model_push M idxName SmtType.Int
                    (SmtValue.Numeral m))
                  (native_string_lit "@x") SmtType.Int v) ty =
              SmtValue.Seq (native_pack_seq T ys) := fun v =>
          hYAt _ (agrees_push_push M idxName SmtType.Int
            (SmtValue.Numeral m) _ _ v)
        have hXMkPush : ∀ v : SmtValue,
            __smtx_model_eval
                (native_model_push
                  (native_model_push M idxName SmtType.Int
                    (SmtValue.Numeral m))
                  (native_string_lit "@x") SmtType.Int v) tx =
              SmtValue.Seq (native_pack_seq T rs) := fun v =>
          hXAt _ (agrees_push_push M idxName SmtType.Int
            (SmtValue.Numeral m) _ _ v)
        have hIdxMkPush : ∀ v : SmtValue,
            __smtx_model_eval
                (native_model_push
                  (native_model_push M idxName SmtType.Int
                    (SmtValue.Numeral m))
                  (native_string_lit "@x") SmtType.Int v) idx =
              SmtValue.Numeral m := by
          intro v
          simp only [idx]
          rw [eval_var_term_eq,
            var_lookup_push_ne _ _ _ _ _ _ str_index_ne_x]
          exact var_lookup_push_same M idxName SmtType.Int _
        have hNilMk :
            __smtx_model_eval
                (native_model_push M idxName SmtType.Int
                  (SmtValue.Numeral m)) nilSegS =
              SmtValue.Seq (SmtSeq.empty T) := by
          simpa [nilSegS] using
            eval_nil_str_concat_typeof_of_smt_type_seq _ segEO T hSegEoTy
        by_cases hm0 : 0 ≤ m
        · by_cases hmK : m < ((occEnds ys zs).length : Int)
          · -- in range: the scan recurrence holds
            have hmmK : Int.toNat m < (occEnds ys zs).length := by first
              | omega
              | (unfold native_Int at *; omega)
            have hIdxMk' :
                __smtx_model_eval
                    (native_model_push M idxName SmtType.Int
                      (SmtValue.Numeral m)) idx =
                  SmtValue.Numeral ((Int.toNat m : Nat) : Int) := by
              rw [hIdxMk]
              congr 1
              exact (Int.toNat_of_nonneg hm0).symm
            have hOiIdxMk := oi_eval
              (native_model_push M idxName SmtType.Int
                (SmtValue.Numeral m))
              tz ty idx T zs ys (Int.toNat m) hZMk hYMk
              hIdxMk' hYs (Nat.le_of_lt hmmK)
            rcases indexof_at_bound ys zs hYs (Int.toNat m) hmmK with
              ⟨hPatLe, hMono, hIdxAt⟩
            have hINextMk :
                __smtx_model_eval
                    (native_model_push M idxName SmtType.Int
                      (SmtValue.Numeral m)) iNext =
                  SmtValue.Numeral ((Int.toNat m + 1 : Nat) : Int) := by
              simp only [iNext]
              rw [StrSubstrContainsSupport.smtx_eval_plus_term_eq,
                StrSubstrContainsSupport.smtx_eval_plus_term_eq,
                hIdxMk, eval_numeral_term_eq, eval_numeral_term_eq]
              simp only [__smtx_model_eval_plus, native_zplus]
              congr 1
              first
              | omega
              | (unfold native_Int at *; omega)
            have hOiNextMk := oi_eval
              (native_model_push M idxName SmtType.Int
                (SmtValue.Numeral m))
              tz ty iNext T zs ys (Int.toNat m + 1) hZMk hYMk
              hINextMk hYs (by first
              | omega
              | (unfold native_Int at *; omega))
            have hRarIdxMk :
                __smtx_model_eval
                    (native_model_push M idxName SmtType.Int
                      (SmtValue.Numeral m)) (rarT idx) =
                  SmtValue.Seq
                    (native_pack_seq T
                      (native_seq_replace_all
                        (zs.drop (bound ys zs (Int.toNat m))) ys rs)) := by
              simp only [rarT, sourceLen]
              exact rar_eval _ tz ty tx idx T zs ys rs (Int.toNat m)
                hZMk hYMk hXMk hIdxMk' hYs
                (Nat.le_of_lt hmmK)
            have hRarNextMk :
                __smtx_model_eval
                    (native_model_push M idxName SmtType.Int
                      (SmtValue.Numeral m)) (rarT iNext) =
                  SmtValue.Seq
                    (native_pack_seq T
                      (native_seq_replace_all
                        (zs.drop (bound ys zs (Int.toNat m + 1))) ys
                        rs)) := by
              simp only [rarT, sourceLen]
              exact rar_eval _ tz ty tx iNext T zs ys rs (Int.toNat m + 1)
                hZMk hYMk hXMk hINextMk hYs
                (by first
              | omega
              | (unfold native_Int at *; omega))
            have hStartIMk :
                __smtx_model_eval
                    (native_model_push M idxName SmtType.Int
                      (SmtValue.Numeral m)) startI =
                  SmtValue.Numeral
                    ((bound ys zs (Int.toNat m + 1) - ys.length : Nat) :
                      Int) := by
              simp only [startI]
              rw [eval_str_indexof_term_eq, hZMk, hYMk, hOiIdxMk]
              simp only [__smtx_model_eval_str_indexof,
                Smtm.native_unpack_pack_seq, elem_typeof_pack_seq]
              rw [hIdxAt]
            have hSegMk :
                __smtx_model_eval
                    (native_model_push M idxName SmtType.Int
                      (SmtValue.Numeral m)) seg =
                  SmtValue.Seq
                    (native_pack_seq T
                      ((zs.drop (bound ys zs (Int.toNat m))).take
                        ((bound ys zs (Int.toNat m + 1) - ys.length) -
                          bound ys zs (Int.toNat m)))) := by
              simp only [seg]
              rw [StrSubstrContainsSupport.smtx_eval_str_substr_term_eq,
                hZMk, hOiIdxMk, eval_neg_term_eq, hStartIMk, hOiIdxMk]
              simp only [__smtx_model_eval__,
                __smtx_model_eval_str_substr, Smtm.native_unpack_pack_seq,
                elem_typeof_pack_seq]
              rw [show (native_zplus
                    ((bound ys zs (Int.toNat m + 1) - ys.length : Nat) :
                      Int)
                    (native_zneg
                      ((bound ys zs (Int.toNat m) : Nat) : Int))) =
                  (((bound ys zs (Int.toNat m + 1) - ys.length) -
                    bound ys zs (Int.toNat m) : Nat) : Int) by
                simp only [native_zplus, native_zneg]
                first
              | omega
              | (unfold native_Int at *; omega)]
              rw [extract_cast_drop_take]
            have hReplStep :=
              replace_all_drop_bound_step ys rs zs hYs (Int.toNat m) hmmK
            have hPackEq :
                native_pack_seq T
                    (native_seq_replace_all
                      (zs.drop (bound ys zs (Int.toNat m))) ys rs) =
                  native_pack_seq T
                    (((zs.drop (bound ys zs (Int.toNat m))).take
                        ((bound ys zs (Int.toNat m + 1) - ys.length) -
                          bound ys zs (Int.toNat m))) ++
                      (rs ++
                        (native_seq_replace_all
                            (zs.drop (bound ys zs (Int.toNat m + 1))) ys
                            rs ++
                          []))) := by
              rw [hReplStep]
              simp [List.append_assoc]
            have hSumEq :
                (native_zplus
                    ((bound ys zs (Int.toNat m + 1) - ys.length : Nat) :
                      Int)
                    (native_zplus (Int.ofNat ys.length) 0)) =
                  ((bound ys zs (Int.toNat m + 1) : Nat) : Int) := by
              simp only [native_zplus, Int.ofNat_eq_natCast]
              first
              | omega
              | (unfold native_Int at *; omega)
            simp only [qBody, numOcc, eval_or_term_eq,
              smtx_eval_not_term_eq,
              eval_geq_term_eq, eval_lt_term_eq, eval_and_term_eq,
              eval_eq_term_eq,
              StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
              StrSubstrContainsSupport.smtx_eval_plus_term_eq,
              smtx_eval_str_len_term_eq, eval_numeral_term_eq,
              eval_boolean_term_eq, hIdxMk, hNumOccMk, hStartIMk,
              hRarIdxMk, hRarNextMk, hSegMk, hNilMk, hOiNextMk, hXMk,
              hYMk]
            simp only [__smtx_model_eval_or, __smtx_model_eval_and,
              __smtx_model_eval_not, __smtx_model_eval_eq,
              __smtx_model_eval_geq, __smtx_model_eval_leq,
              __smtx_model_eval_lt, __smtx_model_eval_plus,
              __smtx_model_eval_str_concat, __smtx_model_eval_str_len,
              Smtm.native_unpack_pack_seq, elem_typeof_pack_seq,
              native_seq_concat, native_seq_len, hPackEq, hSumEq]
            simp [native_veq, native_zleq, native_zlt, native_not,
              native_and, native_or, veq_refl_true, native_zplus,
              native_zneg, native_seq_len, Int.ofNat_eq_natCast,
              SmtValue.Numeral.injEq, SmtValue.Seq.injEq,
              native_unpack_seq, List.append_nil]
            first
              | omega
              | (unfold native_Int at *; omega)
              | skip
          · -- past the count: the second guard discharges the clause
            obtain ⟨mi, hOiIdxShape⟩ :
                ∃ mi : Int,
                  __smtx_model_eval
                      (native_model_push M idxName SmtType.Int
                        (SmtValue.Numeral m))
                      (SmtTerm._at_strings_occur_index tz ty idx) =
                    SmtValue.Numeral mi := by
              rw [oi_term_eq, hZMk, hYMk, hIdxMk]
              simp only [__smtx_model_eval__at_strings_occur_index]
              exact ⟨_, rfl⟩
            obtain ⟨mj, hOiNextShape⟩ :
                ∃ mj : Int,
                  __smtx_model_eval
                      (native_model_push M idxName SmtType.Int
                        (SmtValue.Numeral m))
                      (SmtTerm._at_strings_occur_index tz ty iNext) =
                    SmtValue.Numeral mj := by
              rw [oi_term_eq]
              simp only [iNext,
                StrSubstrContainsSupport.smtx_eval_plus_term_eq, hZMk,
                hYMk, hIdxMk, eval_numeral_term_eq, __smtx_model_eval_plus,
                __smtx_model_eval__at_strings_occur_index]
              exact ⟨_, rfl⟩
            simp only [qBody, rarT, seg, startI, sourceLen, numOcc,
              eval_or_term_eq, smtx_eval_not_term_eq, eval_geq_term_eq,
              eval_lt_term_eq, eval_and_term_eq, eval_eq_term_eq,
              eval_str_indexof_term_eq, eval_str_replace_all_term_eq,
              StrSubstrContainsSupport.smtx_eval_str_substr_term_eq,
              StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
              StrSubstrContainsSupport.smtx_eval_plus_term_eq,
              smtx_eval_str_len_term_eq, eval_numeral_term_eq,
              eval_neg_term_eq, eval_boolean_term_eq, hIdxMk, hNumOccMk,
              hOiIdxShape, hOiNextShape, hZMk, hYMk, hXMk, hNilMk]
            simp only [__smtx_model_eval_or, __smtx_model_eval_and,
              __smtx_model_eval_not, __smtx_model_eval_eq,
              __smtx_model_eval_geq, __smtx_model_eval_leq,
              __smtx_model_eval_lt, __smtx_model_eval_plus,
              __smtx_model_eval__, __smtx_model_eval_str_indexof,
              __smtx_model_eval_str_substr,
              __smtx_model_eval_str_replace_all,
              __smtx_model_eval_str_concat, __smtx_model_eval_str_len,
              Smtm.native_unpack_pack_seq, elem_typeof_pack_seq]
            have hB : native_zlt m ((occEnds ys zs).length : Int) =
                false := by
              simp only [native_zlt, decide_eq_false_iff_not]
              first
              | omega
              | (unfold native_Int at *; omega)
            simp [native_zleq, native_zlt, native_not, native_and,
              native_or, hB]
            refine Or.inr (Or.inl ?_)
            first
              | omega
              | (unfold native_Int at *; omega)
        · -- negative index: the first guard discharges the clause
          obtain ⟨mi, hOiIdxShape⟩ :
              ∃ mi : Int,
                __smtx_model_eval
                    (native_model_push M idxName SmtType.Int
                      (SmtValue.Numeral m))
                    (SmtTerm._at_strings_occur_index tz ty idx) =
                  SmtValue.Numeral mi := by
            rw [oi_term_eq, hZMk, hYMk, hIdxMk]
            simp only [__smtx_model_eval__at_strings_occur_index]
            exact ⟨_, rfl⟩
          obtain ⟨mj, hOiNextShape⟩ :
              ∃ mj : Int,
                __smtx_model_eval
                    (native_model_push M idxName SmtType.Int
                      (SmtValue.Numeral m))
                    (SmtTerm._at_strings_occur_index tz ty iNext) =
                  SmtValue.Numeral mj := by
            rw [oi_term_eq]
            simp only [iNext,
              StrSubstrContainsSupport.smtx_eval_plus_term_eq, hZMk,
              hYMk, hIdxMk, eval_numeral_term_eq, __smtx_model_eval_plus,
              __smtx_model_eval__at_strings_occur_index]
            exact ⟨_, rfl⟩
          simp only [qBody, rarT, seg, startI, sourceLen, numOcc,
            eval_or_term_eq, smtx_eval_not_term_eq, eval_geq_term_eq,
            eval_lt_term_eq, eval_and_term_eq, eval_eq_term_eq,
            eval_str_indexof_term_eq, eval_str_replace_all_term_eq,
            StrSubstrContainsSupport.smtx_eval_str_substr_term_eq,
            StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
            StrSubstrContainsSupport.smtx_eval_plus_term_eq,
            smtx_eval_str_len_term_eq, eval_numeral_term_eq,
            eval_neg_term_eq, eval_boolean_term_eq, hIdxMk, hNumOccMk,
            hOiIdxShape, hOiNextShape, hZMk, hYMk, hXMk, hNilMk]
          simp only [__smtx_model_eval_or, __smtx_model_eval_and,
            __smtx_model_eval_not, __smtx_model_eval_eq,
            __smtx_model_eval_geq, __smtx_model_eval_leq,
            __smtx_model_eval_lt, __smtx_model_eval_plus,
            __smtx_model_eval__, __smtx_model_eval_str_indexof,
            __smtx_model_eval_str_substr,
            __smtx_model_eval_str_replace_all,
            __smtx_model_eval_str_concat, __smtx_model_eval_str_len,
            Smtm.native_unpack_pack_seq, elem_typeof_pack_seq]
          have hA : native_zleq 0 m = false := by
            simp only [native_zleq, decide_eq_false_iff_not]
            first
              | omega
              | (unfold native_Int at *; omega)
          simp [native_zleq, native_zlt, native_not, native_and,
            native_or, hA]
          try
            (refine Or.inl ?_
             first
               | omega
               | (unfold native_Int at *; omega))
      -- assemble
      rw [smtx_eval_and_term_eq, smtx_eval_and_term_eq,
        smtx_eval_and_term_eq, smtx_eval_and_term_eq,
        smtx_eval_and_term_eq, smtx_eval_and_term_eq,
        hC1, hC2, hC3, hC4, hC5, hC6, eval_boolean_term_eq]
      simp [__smtx_model_eval_and, native_and]
