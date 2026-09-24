module

public import Cpc.Proofs.Canonical.Basic
import all Cpc.Proofs.Canonical.Basic

public section

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

/-- Empty sequence values are canonical. -/
theorem seq_canonical_empty (T : SmtType) :
    __smtx_seq_canonical (SmtSeq.empty T) = true := by
  simp [__smtx_seq_canonical]

/-- Consing a canonical value onto a canonical sequence preserves sequence canonicality. -/
theorem seq_canonical_cons
    {v : SmtValue}
    {s : SmtSeq}
    (hv : value_canonical v)
    (hs : __smtx_seq_canonical s = true) :
    __smtx_seq_canonical (SmtSeq.cons v s) = true := by
  have hvBool : __smtx_value_canonical v = true := by
    simpa [value_canonical] using hv
  simp [__smtx_seq_canonical, hvBool, hs, SmtEval.native_and]

/-- Canonical sequences give canonical `Seq` values. -/
theorem value_canonical_seq_of_seq_canonical
    {s : SmtSeq}
    (h : __smtx_seq_canonical s = true) :
    value_canonical (SmtValue.Seq s) := by
  simpa [value_canonical, __smtx_value_canonical] using h

/-- Packing and then unpacking a list of values gives the original list. -/
theorem native_unpack_pack_seq (T : SmtType) :
    ∀ xs : List SmtValue, native_unpack_seq (native_pack_seq T xs) = xs
  | [] => by
      simp [native_pack_seq, native_unpack_seq]
  | x :: xs => by
      simp [native_pack_seq, native_unpack_seq, native_unpack_pack_seq T xs]

/-- Packing a list of canonical values gives a canonical sequence. -/
theorem seq_canonical_pack_seq
    (T : SmtType) :
    ∀ {xs : List SmtValue},
      (∀ v, v ∈ xs -> value_canonical v) ->
        __smtx_seq_canonical (native_pack_seq T xs) = true
  | [], _h => by
      simp [native_pack_seq, __smtx_seq_canonical]
  | v :: vs, h => by
      have hv : value_canonical v := h v (by simp)
      have hvs : ∀ u, u ∈ vs -> value_canonical u := by
        intro u hu
        exact h u (by simp [hu])
      simpa [native_pack_seq] using
        seq_canonical_cons hv (seq_canonical_pack_seq T hvs)

/-- Unpacking a canonical sequence gives a list of canonical values. -/
theorem seq_unpack_values_canonical :
    ∀ {s : SmtSeq},
      __smtx_seq_canonical s = true ->
        ∀ v, v ∈ native_unpack_seq s -> value_canonical v
  | SmtSeq.empty T, _h, v, hv => by
      simp [native_unpack_seq] at hv
  | SmtSeq.cons x xs, h, v, hv => by
      have hx : value_canonical x := by
        have hParts := h
        simp [__smtx_seq_canonical, SmtEval.native_and] at hParts
        exact hParts.1
      have hxs : __smtx_seq_canonical xs = true := by
        have hParts := h
        simp [__smtx_seq_canonical, SmtEval.native_and] at hParts
        exact hParts.2
      simp [native_unpack_seq] at hv
      rcases hv with rfl | hv
      · exact hx
      · exact seq_unpack_values_canonical hxs v hv

/-- Repacking the concatenation of two canonical sequences is canonical. -/
theorem seq_canonical_pack_unpack_concat
    (T : SmtType)
    {s1 s2 : SmtSeq}
    (h1 : __smtx_seq_canonical s1 = true)
    (h2 : __smtx_seq_canonical s2 = true) :
    __smtx_seq_canonical
      (native_pack_seq T (native_unpack_seq s1 ++ native_unpack_seq s2)) = true := by
  apply seq_canonical_pack_seq
  intro v hv
  simp at hv
  rcases hv with hv | hv
  · exact seq_unpack_values_canonical h1 v hv
  · exact seq_unpack_values_canonical h2 v hv

/-- Repacking the reverse of a canonical sequence is canonical. -/
theorem seq_canonical_pack_unpack_reverse
    (T : SmtType)
    {s : SmtSeq}
    (h : __smtx_seq_canonical s = true) :
    __smtx_seq_canonical
      (native_pack_seq T (native_unpack_seq s).reverse) = true := by
  apply seq_canonical_pack_seq
  intro v hv
  exact seq_unpack_values_canonical h v (by simpa using hv)

/-- Repacking a canonical sequence is canonical, even under a different empty-sequence tag. -/
theorem seq_canonical_pack_unpack
    (T : SmtType)
    {s : SmtSeq}
    (h : __smtx_seq_canonical s = true) :
    __smtx_seq_canonical (native_pack_seq T (native_unpack_seq s)) = true := by
  apply seq_canonical_pack_seq
  intro v hv
  exact seq_unpack_values_canonical h v hv

/-- Repacking a subsequence extracted from a canonical sequence is canonical. -/
theorem seq_canonical_pack_unpack_extract
    (T : SmtType)
    {s : SmtSeq}
    (h : __smtx_seq_canonical s = true)
    (i n : native_Int) :
    __smtx_seq_canonical
      (native_pack_seq T (native_seq_extract (native_unpack_seq s) i n)) = true := by
  apply seq_canonical_pack_seq
  intro v hv
  simp [native_seq_extract] at hv
  exact seq_unpack_values_canonical h v
    (List.mem_of_mem_drop (List.mem_of_mem_take hv.2))

/-- Repacking a one-shot replacement of canonical sequences is canonical. -/
theorem seq_canonical_pack_unpack_replace
    (T : SmtType)
    {s pat repl : SmtSeq}
    (hs : __smtx_seq_canonical s = true)
    (_hpat : __smtx_seq_canonical pat = true)
    (hrepl : __smtx_seq_canonical repl = true) :
    __smtx_seq_canonical
      (native_pack_seq T
        (native_seq_replace (native_unpack_seq s)
          (native_unpack_seq pat) (native_unpack_seq repl))) = true := by
  unfold native_seq_replace native_str_replace_re
  cases hFind : native_re_find_idx_from
      (native_str_to_re (native_unpack_seq pat)) (native_unpack_seq s) 0 with
  | none =>
      simpa [hFind] using seq_canonical_pack_unpack T hs
  | some found =>
      rcases found with ⟨idx, len⟩
      simp [hFind]
      apply seq_canonical_pack_seq
      intro v hv
      simp [List.mem_append] at hv
      rcases hv with hv | hv | hv
      · exact seq_unpack_values_canonical hs v (List.mem_of_mem_take hv)
      · exact seq_unpack_values_canonical hrepl v hv
      · exact seq_unpack_values_canonical hs v (List.mem_of_mem_drop hv)

/-- Repacking a regex replacement of canonical value sequences is canonical. -/
theorem seq_canonical_pack_unpack_replace_re
    (T : SmtType)
    {s repl : SmtSeq}
    (r : SmtRegLan)
    (hs : __smtx_seq_canonical s = true)
    (hrepl : __smtx_seq_canonical repl = true) :
    __smtx_seq_canonical
      (native_pack_seq T
        (native_str_replace_re (native_unpack_seq s) r
          (native_unpack_seq repl))) = true := by
  unfold native_str_replace_re
  cases hFind : native_re_find_idx_from r (native_unpack_seq s) 0 with
  | none =>
      simpa [hFind] using seq_canonical_pack_unpack T hs
  | some found =>
      rcases found with ⟨idx, len⟩
      simp [hFind]
      apply seq_canonical_pack_seq
      intro v hv
      simp [List.mem_append] at hv
      rcases hv with hv | hv | hv
      · exact seq_unpack_values_canonical hs v (List.mem_of_mem_take hv)
      · exact seq_unpack_values_canonical hrepl v hv
      · exact seq_unpack_values_canonical hs v (List.mem_of_mem_drop hv)

/-- Auxiliary canonicality invariant for repeated sequence replacement. -/
theorem seq_canonical_pack_replace_all_aux
    (T : SmtType)
    {r : SmtRegLan} {repl : List SmtValue}
    (hrepl : ∀ v, v ∈ repl -> value_canonical v) :
    ∀ (fuel : Nat) {xs : List SmtValue},
      (∀ v, v ∈ xs -> value_canonical v) ->
        __smtx_seq_canonical
          (native_pack_seq T
            (impl_native_re_replace_all_nonempty_list_aux fuel r repl xs)) = true
  | 0, xs, hxs => by
      simpa [impl_native_re_replace_all_nonempty_list_aux] using
        seq_canonical_pack_seq T hxs
  | fuel + 1, xs, hxs => by
      cases hMatch : native_re_positive_prefix_match_len? r xs with
      | none =>
          cases xs with
          | nil =>
              simpa [impl_native_re_replace_all_nonempty_list_aux, hMatch] using
                seq_canonical_pack_seq T hxs
          | cons x xs =>
              have hx : value_canonical x := hxs x List.mem_cons_self
              have htail : ∀ u, u ∈ xs -> value_canonical u :=
                fun u hu => hxs u (List.mem_cons_of_mem x hu)
              apply seq_canonical_pack_seq
              intro u hu
              simp [impl_native_re_replace_all_nonempty_list_aux, hMatch] at hu
              rcases hu with rfl | hu
              · exact hx
              · exact seq_unpack_values_canonical
                  (seq_canonical_pack_replace_all_aux T hrepl fuel
                    htail) u
                  (by simpa [native_unpack_pack_seq] using hu)
      | some len =>
          cases len with
          | zero =>
              cases xs with
              | nil =>
                  simpa [impl_native_re_replace_all_nonempty_list_aux, hMatch] using
                    seq_canonical_pack_seq T hxs
              | cons x xs =>
                  have hx : value_canonical x := hxs x List.mem_cons_self
                  have htail : ∀ u, u ∈ xs -> value_canonical u :=
                    fun u hu => hxs u (List.mem_cons_of_mem x hu)
                  apply seq_canonical_pack_seq
                  intro u hu
                  simp [impl_native_re_replace_all_nonempty_list_aux, hMatch] at hu
                  rcases hu with rfl | hu
                  · exact hx
                  · exact seq_unpack_values_canonical
                      (seq_canonical_pack_replace_all_aux T hrepl fuel
                        htail) u
                      (by simpa [native_unpack_pack_seq] using hu)
          | succ len =>
              apply seq_canonical_pack_seq
              intro v hv
              simp [impl_native_re_replace_all_nonempty_list_aux, hMatch,
                List.mem_append] at hv
              rcases hv with hv | hv
              · exact hrepl v hv
              · exact seq_unpack_values_canonical
                  (seq_canonical_pack_replace_all_aux T hrepl fuel
                    (fun u hu => hxs u (List.mem_of_mem_drop hu))) v
                  (by simpa [native_unpack_pack_seq] using hv)

/-- Repacking a repeated replacement of canonical sequences is canonical. -/
theorem seq_canonical_pack_unpack_replace_all
    (T : SmtType)
    {s pat repl : SmtSeq}
    (hs : __smtx_seq_canonical s = true)
    (_hpat : __smtx_seq_canonical pat = true)
    (hrepl : __smtx_seq_canonical repl = true) :
    __smtx_seq_canonical
      (native_pack_seq T
        (native_seq_replace_all (native_unpack_seq s)
          (native_unpack_seq pat) (native_unpack_seq repl))) = true := by
  unfold native_seq_replace_all
  unfold native_str_replace_re_all impl_native_re_replace_all_nonempty_list
  exact seq_canonical_pack_replace_all_aux T
    (fun u hu => seq_unpack_values_canonical hrepl u hu)
    ((native_unpack_seq s).length + 1)
    (fun u hu => seq_unpack_values_canonical hs u hu)

/-- Repacking regex replace-all over canonical value sequences is canonical. -/
theorem seq_canonical_pack_unpack_replace_re_all
    (T : SmtType)
    {s repl : SmtSeq}
    (r : SmtRegLan)
    (hs : __smtx_seq_canonical s = true)
    (hrepl : __smtx_seq_canonical repl = true) :
    __smtx_seq_canonical
      (native_pack_seq T
        (native_str_replace_re_all (native_unpack_seq s) r
          (native_unpack_seq repl))) = true := by
  unfold native_str_replace_re_all impl_native_re_replace_all_nonempty_list
  exact seq_canonical_pack_replace_all_aux T
    (fun u hu => seq_unpack_values_canonical hrepl u hu)
    ((native_unpack_seq s).length + 1)
    (fun u hu => seq_unpack_values_canonical hs u hu)

/-- Repacking a sequence update with canonical replacement values is canonical. -/
theorem seq_canonical_pack_unpack_update
    (T : SmtType)
    {s repl : SmtSeq}
    (hs : __smtx_seq_canonical s = true)
    (hrepl : __smtx_seq_canonical repl = true)
    (i : native_Int) :
    __smtx_seq_canonical
      (native_pack_seq T
        (native_seq_update (native_unpack_seq s) i (native_unpack_seq repl))) = true := by
  apply seq_canonical_pack_seq
  intro v hv
  unfold native_seq_update at hv
  dsimp at hv
  generalize hb :
    (decide (i < 0) ||
      decide (Int.ofNat (native_unpack_seq s).length ≤ i)) = b at hv
  cases b
  · simp [List.mem_append] at hv
    rcases hv with hv | hv | hv
    · exact seq_unpack_values_canonical hs v
        (List.mem_of_mem_take hv)
    · exact seq_unpack_values_canonical hrepl v
        (List.mem_of_mem_take hv)
    · exact seq_unpack_values_canonical hs v
        (List.mem_of_mem_drop hv)
  · simp at hv
    exact seq_unpack_values_canonical hs v hv

/-- Unpacking a canonical sequence yields a valid native string. -/
theorem native_unpack_string_valid_of_seq_canonical
    {s : SmtSeq}
    (hs : __smtx_seq_canonical s = true) :
    native_string_valid (native_unpack_string s) = true := by
  unfold native_unpack_string
  rw [native_string_valid, List.all_eq_true]
  intro c hc
  rcases List.mem_map.mp hc with ⟨v, hv, rfl⟩
  have hvCan : value_canonical v :=
    seq_unpack_values_canonical hs v hv
  cases v <;>
    simp [impl_native_ssm_char_of_value, native_char_valid,
      value_canonical, __smtx_value_canonical] at hvCan ⊢
  exact decide_eq_true hvCan

/-- Packing a valid native string gives a canonical sequence. -/
theorem seq_canonical_pack_string
    (s : native_String)
    (hs : native_string_valid s = true) :
    __smtx_seq_canonical (native_pack_string s) = true := by
  unfold native_pack_string
  apply seq_canonical_pack_seq
  intro v hv
  rcases List.mem_map.mp hv with ⟨c, hc, rfl⟩
  have hcValid : native_char_valid c = true := by
    rw [native_string_valid, List.all_eq_true] at hs
    exact hs c hc
  exact value_canonical_char c hcValid

theorem value_canonical_string
    (s : native_String)
    (hs : native_string_valid s = true) :
    value_canonical (SmtValue.Seq (native_pack_string s)) := by
  exact value_canonical_seq_of_seq_canonical (seq_canonical_pack_string s hs)

theorem value_canonical_seq_empty (T : SmtType) :
    value_canonical (SmtValue.Seq (SmtSeq.empty T)) := by
  exact value_canonical_seq_of_seq_canonical (seq_canonical_empty T)

theorem value_canonical_seq_cons
    {v : SmtValue}
    {s : SmtSeq}
    (hv : value_canonical v)
    (hs : __smtx_seq_canonical s = true) :
    value_canonical (SmtValue.Seq (SmtSeq.cons v s)) := by
  exact value_canonical_seq_of_seq_canonical (seq_canonical_cons hv hs)

end Smtm
